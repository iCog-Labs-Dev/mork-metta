//! Syntax dispatch for machine evaluation.

use super::budget::plain;
use super::frame::Frame;
use super::state::Transition;
use super::task::{Head, Task};
use crate::env::Env;
use crate::func::{FnTable, FunctionKind};
use crate::parser::Expr;
use std::sync::Arc;

/// Schedule evaluation for a unary form resumed by a frame.
pub(crate) fn push_unary(
    name: &str,
    args: &[Expr],
    env: &Env,
    work: &mut Vec<Task>,
    frame: Frame,
) -> Result<(), String> {
    if args.len() != 1 {
        return Err(format!("{name}: expected 1 arg, got {}", args.len()));
    }
    work.push(Task::Apply(frame));
    work.push(Task::Eval {
        expr: Arc::new(args[0].clone()),
        env: env.clone(),
    });
    Ok(())
}

/// Dispatch an `if` form by evaluating its condition with full env tracking
/// and threading discovered bindings into branch environments.
pub(crate) fn dispatch_if(args: &[Expr], env: &Env, funcs: &FnTable, work: &mut Vec<Task>) -> Result<(), String> {
    if args.len() < 2 || args.len() > 3 {
        return Err(format!("if: expected 2 or 3 args, got {}", args.len()));
    }
    let condition_rs = super::step::run_rs(
        Arc::new(args[0].clone()),
        env.clone(),
        funcs,
        &mut None,
    )?;
    let then_expr = &args[1];
    let else_expr = args.get(2);
    let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
    let mut had_bindings = false;
    for (cond, cond_env) in &condition_rs {
        if !matches!(cond_env, Env::Empty) {
            had_bindings = true;
        }
        if crate::eval::forms::control::is_truthy(cond) {
            let branch_env = crate::eval::shared::pattern::prepend_env(
                cond_env.clone(),
                env,
            );
            branches.push((Arc::new(then_expr.clone()), branch_env));
        } else if let Some(else_expr) = else_expr {
            branches.push((Arc::new(else_expr.clone()), env.clone()));
        }
    }
    work.push(Task::Apply(Frame::IfGather { had_bindings, n: branches.len() }));
    for (branch, branch_env) in branches.into_iter().rev() {
        work.push(Task::Eval { expr: branch, env: branch_env });
    }
    Ok(())
}

/// Dispatch a `case` form by evaluating its scrutinee and deferring branch choice.
pub(crate) fn dispatch_case(args: &[Expr], env: &Env, work: &mut Vec<Task>) -> Result<(), String> {
    if args.len() != 2 {
        return Err(format!("case: expected 2 args, got {}", args.len()));
    }
    let clauses = match &args[1] {
        Expr::List(items) => items,
        other => return Err(format!("case: expected clause list, got {}", other.to_string())),
    };
    work.push(Task::Apply(Frame::CaseSelect {
        clauses: Arc::new(clauses.clone()),
        env: env.clone(),
    }));
    work.push(Task::Eval {
        expr: Arc::new(args[0].clone()),
        env: env.clone(),
    });
    Ok(())
}

/// Dispatch a single expression into machine work or a direct result.
pub(crate) fn dispatch_expr(
    expr: &Expr,
    env: &Env,
    funcs: &crate::func::FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<super::budget::ResultSet>,
) -> Result<(), String> {
    match expr {
        Expr::Number(number) => {
            vals.push(plain(vec![crate::atom::Atom::Num(number.clone())]));
            Ok(())
        }
        Expr::Symbol(symbol) => {
            let atom = if symbol.starts_with('$') {
                crate::eval::shared::env::lookup(env, symbol)
                    .unwrap_or_else(|| crate::atom::Atom::sym(symbol))
            } else {
                crate::atom::Atom::sym(symbol)
            };
            vals.push(plain(vec![atom]));
            Ok(())
        }
        Expr::Str(s) => {
            vals.push(plain(vec![crate::atom::Atom::str_val(s)]));
            Ok(())
        }
        Expr::List(items) => {
            if items.is_empty() {
                vals.push(plain(vec![crate::atom::Atom::Expr(Vec::new())]));
                return Ok(());
            }

            if let Expr::Symbol(head) = &items[0] {
                let args = &items[1..];
                match head.as_str() {
                    "cut" => {
                        // cut returns true and prunes remaining alternative branches
                        // from the work queue (innermost Gather/IfGather -> n=1).
                        vals.push(plain(vec![crate::atom::Atom::sym("true")]));
                        if let Some(gather_idx) = work.iter().rposition(|t| {
                            matches!(t, super::task::Task::Apply(Frame::Gather { .. } | Frame::IfGather { .. }))
                        }) {
                            let current = work.len().saturating_sub(1);
                            if current > gather_idx + 1 {
                                work.drain(gather_idx + 1 .. current);
                            }
                            if let Some(super::task::Task::Apply(frame)) = work.get_mut(gather_idx) {
                                match frame {
                                    Frame::Gather { n } => *n = 1,
                                    Frame::IfGather { n, .. } => *n = 1,
                                    _ => {}
                                }
                            }
                        }
                        return Ok(());
                    }
                    "quote" => {
                        if args.len() != 1 {
                            return Err(format!("quote: expected 1 arg, got {}", args.len()));
                        }
                        vals.push(plain(vec![crate::eval::forms::immediate::quote_atom(
                            &args[0], env,
                        )]));
                        return Ok(());
                    }
                    "call" | "reduce" => {
                        if args.len() != 1 {
                            return Err(format!("{}: expected 1 arg, got {}", head, args.len()));
                        }
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "eval" => {
                        if args.len() != 1 {
                            return Err(format!("eval: expected 1 arg, got {}", args.len()));
                        }
                        let (target, tenv) = match &args[0] {
                            Expr::Symbol(v) if v.starts_with('$') => {
                                let val = env
                                    .get(v)
                                    .ok_or_else(|| format!("eval: unbound variable {}", v))?;
                                match &val {
                                    crate::atom::Atom::Closure(c) if c.params.is_empty() => {
                                        (c.body.clone(), c.env.clone())
                                    }
                                    _ => {
                                        let expr = crate::parser::atom_to_expr(&val)?;
                                        (expr, env.clone())
                                    }
                                }
                            }
                            other => (other.clone(), env.clone()),
                        };
                        work.push(Task::Eval {
                            expr: Arc::new(target),
                            env: tenv,
                        });
                        return Ok(());
                    }
                    "|->" => {
                        if args.len() != 2 {
                            return Err(format!("|->: expected (params body), got {} args", args.len()));
                        }
                        let params = match &args[0] {
                            Expr::List(items) => items.clone(),
                            other => vec![other.clone()],
                        };
                        let body = args[1].clone();
                        vals.push(plain(vec![crate::atom::Atom::Closure(Box::new(
                            crate::atom::ClosureData {
                                params,
                                body,
                                env: env.clone(),
                            },
                        ))]));
                        return Ok(());
                    }

                    "empty" => {
                        vals.push(Vec::new());
                        return Ok(());
                    }
                    "import!" => {
                        if args.len() != 2 {
                            return Err(format!("import!: expected 2 args, got {}", args.len()));
                        }
                        let path = match &args[1] {
                            Expr::Symbol(s) => s.clone(),
                            _ => return Err("import!: path must be a symbol".into()),
                        };
                        work.push(Task::Apply(Frame::ImportFile {
                            path,
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "import-rs!" => {
                        // import-rs! is a plugin-only form; keep as direct call for now
                        let nd = crate::eval::io::eval_import_rs(args, env, funcs)?;
                        vals.push(plain(nd.collect()));
                        return Ok(());
                    }
                    "println!" => {
                        if args.len() != 1 {
                            return Err(format!("println!: expected 1 arg, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::Println));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "readln!" => {
                        let nd = crate::eval::io::eval_readln(&[], env, funcs)?;
                        vals.push(plain(nd.collect()));
                        return Ok(());
                    }
                    "foldall" => {
                        if args.len() != 3 {
                            return Err(format!("foldall: expected (agg-func gen-expr init), got {} args", args.len()));
                        }
                        let gen_rs = super::step::run_rs(Arc::new(args[1].clone()), env.clone(), funcs, &mut None)?;
                        let gen_values: Vec<crate::atom::Atom> = gen_rs.into_iter().map(|(a, _)| a).collect();
                        let init_rs = super::step::run_rs(Arc::new(args[2].clone()), env.clone(), funcs, &mut None)?;
                        let init = init_rs.into_iter().next().map(|(a, _)| a)
                            .ok_or_else(|| "foldall: init produced no result".to_string())?;
                        // Evaluate agg_func expression to an atom once so inline lambdas
                        // are resolved to closures before the fold loop
                        let agg_atom = super::step::run_rs(Arc::new(args[0].clone()), env.clone(), funcs, &mut None)?
                            .into_iter().next().map(|(a, _)| a)
                            .ok_or_else(|| "foldall: agg-func produced no value".to_string())?;
                        let (agg_head, agg_env) = match &agg_atom {
                            crate::atom::Atom::Sym(name) => {
                                (Expr::Symbol(name.to_string()), env.clone())
                            }
                            crate::atom::Atom::Closure(_) => {
                                (Expr::Symbol("$__foldall_fn".to_string()),
                                 crate::eval::shared::env::bind(env, "$__foldall_fn", agg_atom.clone()))
                            }
                            _ => return Err("foldall: agg-func must be a function symbol or closure".to_string()),
                        };
                        let accum = gen_values.into_iter().try_fold(init, |acc, val| {
                            let acc_expr = crate::parser::atom_to_expr(&acc)?;
                            let val_expr = crate::parser::atom_to_expr(&val)?;
                            let call = Expr::List(vec![agg_head.clone(), acc_expr, val_expr]);
                            super::step::run_rs(Arc::new(call), agg_env.clone(), funcs, &mut None)?
                                .into_iter().next().map(|(a, _)| a)
                                .ok_or_else(|| "foldall: agg-func produced no result".to_string())
                        })?;
                        vals.push(plain(vec![accum]));
                        return Ok(());
                    }
                    "forall" => {
                        if args.len() != 2 {
                            return Err(format!("forall: expected 2 args, got {}", args.len()));
                        }
                        let gen_values: Vec<crate::atom::Atom> =
                            super::step::run_rs(Arc::new(args[0].clone()), env.clone(), funcs, &mut None)?
                                .into_iter().map(|(a, _)| a).collect();
                        let check_atom = super::step::run_rs(Arc::new(args[1].clone()), env.clone(), funcs, &mut None)?
                            .into_iter().next().map(|(a, _)| a)
                            .ok_or_else(|| "forall: check produced no value".to_string())?;
                        let arg_sym = Expr::Symbol("$__fv".to_string());
                        let check_is_closure = matches!(&check_atom, crate::atom::Atom::Closure(_));
                        let check_temp = if check_is_closure {
                            Some(crate::eval::shared::env::bind(env, "$__check_fn", check_atom.clone()))
                        } else {
                            None
                        };
                        for val in gen_values {
                            let call_env = crate::eval::shared::env::bind(env, "$__fv", val);
                            let call_env = if let Some(ref check_env) = check_temp {
                                crate::eval::shared::pattern::prepend_env(check_env.clone(), &call_env)
                            } else {
                                call_env
                            };
                            let results: Vec<crate::atom::Atom> = match &check_atom {
                                crate::atom::Atom::Sym(fname) => {
                                    let call = Expr::List(vec![Expr::Symbol(fname.to_string()), arg_sym.clone()]);
                                    super::step::run_rs(Arc::new(call), call_env, funcs, &mut None)?
                                        .into_iter().map(|(a, _)| a).collect()
                                }
                                crate::atom::Atom::Closure(_) => {
                                    let call = Expr::List(vec![Expr::Symbol("$__check_fn".to_string()), arg_sym.clone()]);
                                    super::step::run_rs(Arc::new(call), call_env, funcs, &mut None)?
                                        .into_iter().map(|(a, _)| a).collect()
                                }
                                _ => return Err("forall: check must be a function symbol or closure".to_string()),
                            };
                            if results.is_empty() || !results.iter().all(|a| crate::eval::forms::control::is_truthy(a)) {
                                vals.push(plain(vec![crate::atom::Atom::sym("false")]));
                                return Ok(());
                            }
                        }
                        vals.push(plain(vec![crate::atom::Atom::sym("true")]));
                        return Ok(());
                    }
                    "foldl-atom" => {
                        if args.len() != 3 {
                            return Err(format!("foldl-atom: expected 3 args, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::FoldlInit));
                        for arg in args.iter().rev() {
                            work.push(Task::Eval {
                                expr: Arc::new((*arg).clone()),
                                env: env.clone(),
                            });
                        }
                        return Ok(());
                    }
                    "if" => return dispatch_if(args, env, funcs, work),
                    "case" => return dispatch_case(args, env, work),
                    "within" => return push_unary("within", args, env, work, Frame::WithinWrap),
                    "collapse" => {
                        return push_unary("collapse", args, env, work, Frame::CollapseGather)
                    }
                    "once" => return push_unary("once", args, env, work, Frame::OnceCut),
                    "superpose" => {
                        if args.len() != 1 {
                            return Err(format!("superpose: expected 1 arg, got {}", args.len()));
                        }
                        if let Expr::List(elems) = &args[0] {
                            let n = elems.len();
                            if n == 0 {
                                vals.push(Vec::new());
                                return Ok(());
                            }
                            work.push(Task::Apply(Frame::Gather { n }));
                            for elem in elems.iter().rev() {
                                work.push(Task::Eval {
                                    expr: Arc::new(elem.clone()),
                                    env: env.clone(),
                                });
                            }
                        } else {
                            work.push(Task::Apply(Frame::SuperposeUnpack));
                            work.push(Task::Eval {
                                expr: Arc::new(args[0].clone()),
                                env: env.clone(),
                            });
                        }
                        return Ok(());
                    }
                    "let" => {
                        if args.len() != 3 {
                            return Err(format!("let: expected 3 args, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::LetMatch {
                            pattern: args[0].clone(),
                            body: Arc::new(args[2].clone()),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[1].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "let*" => {
                        let bindings = crate::eval::forms::control::let_star_bindings(args)?;
                        if bindings.is_empty() {
                            work.push(Task::Eval {
                                expr: Arc::new(args[1].clone()),
                                env: env.clone(),
                            });
                            return Ok(());
                        }
                        let (_, value_expr) =
                            crate::eval::forms::control::let_star_binding(&bindings, 0)?;
                        work.push(Task::Apply(Frame::LetStarBind {
                            bindings: Arc::clone(&bindings),
                            bind_index: 0,
                            body: Arc::new(args[1].clone()),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(value_expr.clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "chain" => {
                        if args.len() < 3 || args.len() % 2 == 0 {
                            return Err(format!(
                                "chain: expected odd number of args >= 3, got {}",
                                args.len()
                            ));
                        }
                        let args_arc = Arc::new(args.to_vec());
                        work.push(Task::Apply(Frame::ChainBind {
                            args: Arc::clone(&args_arc),
                            pair_index: 0,
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "progn" => {
                        if args.len() < 1 {
                            return Err("progn: expected at least one form".into());
                        }
                        // Evaluate all args sequentially, return last result
                        work.push(Task::Apply(Frame::Progn { n: args.len() }));
                        for arg in args.iter().rev() {
                            work.push(Task::Eval {
                                expr: Arc::new(arg.clone()),
                                env: env.clone(),
                            });
                        }
                        return Ok(());
                    }
                    "prog1" => {
                        if args.len() < 1 {
                            return Err("prog1: expected at least one form".into());
                        }
                        // Evaluate all args sequentially, return first result
                        work.push(Task::Apply(Frame::Prog1 { n: args.len() }));
                        for arg in args.iter().rev() {
                            work.push(Task::Eval {
                                expr: Arc::new(arg.clone()),
                                env: env.clone(),
                            });
                        }
                        return Ok(());
                    }
                    "match" => {
                        if args.len() != 3 {
                            return Err(format!("match: expected 3 args, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::SpaceMatch {
                            pattern: args[1].clone(),
                            body: Arc::new(args[2].clone()),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "transform" => {
                        if args.len() != 2 {
                            return Err(format!("transform: expected 2 args, got {}", args.len()));
                        }
                        let pattern = crate::eval::shared::subst::subst_and_atomize(&args[0], env);
                        let replacement =
                            crate::eval::shared::subst::subst_and_atomize(&args[1], env);
                        work.push(Task::Transition(Transition::Transform {
                            pattern,
                            replacement,
                        }));
                        return Ok(());
                    }
                    "with_mutex" => {
                        if args.len() != 2 {
                            return Err(format!("with_mutex: expected 2 args, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::MutexEnter {
                            body: Arc::new(args[1].clone()),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "transaction" => {
                        if args.len() != 1 {
                            return Err(format!("transaction: expected 1 arg, got {}", args.len()));
                        }
                        work.push(Task::Transition(Transition::Transaction {
                            body: Arc::new(args[0].clone()),
                            env: env.clone(),
                        }));
                        return Ok(());
                    }
                    "add-atom" => {
                        if args.len() != 2 {
                            return Err(format!("add-atom: expected 2 args, got {}", args.len()));
                        }
                        work.push(Task::Apply(Frame::SpaceAdd {
                            atom: args[1].clone(),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    "remove-atom" => {
                        if args.len() != 2 {
                            return Err(format!(
                                "remove-atom: expected 2 args, got {}",
                                args.len()
                            ));
                        }
                        work.push(Task::Apply(Frame::SpaceRemove {
                            atom: args[1].clone(),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(args[0].clone()),
                            env: env.clone(),
                        });
                        return Ok(());
                    }
                    _ => {}
                }

                if let Some(function) = funcs.get(head, args.len() as u8) {
                    match &function.kind {
                        FunctionKind::Native { func } => {
                            work.push(Task::Apply(Frame::Call {
                                head: Head::Native(Arc::clone(func)),
                                arity: args.len(),
                                env: env.clone(),
                                prebound_args: None,
                            }));
                            for arg in args.iter().rev() {
                                work.push(Task::Eval {
                                    expr: Arc::new(arg.clone()),
                                    env: env.clone(),
                                });
                            }
                            return Ok(());
                        }
                    }
                }

                if let Some(clauses) =
                    crate::eval::forms::query::lookup_user_clauses(head, args.len() as u8, funcs)
                {
                    let clause_slice: Vec<(&[Expr], &Expr)> =
                        clauses.iter().map(|(p, b)| (p.as_slice(), b)).collect();
                    let lazy_mask =
                        crate::eval::shared::closure::lazy_user_arg_mask(&clause_slice);
                    let clause_refs: Vec<(Vec<Expr>, Expr)> = clauses;
                    let mut prebound_args = Vec::with_capacity(args.len());
                    let mut eager_indices = Vec::new();
                    for (index, arg) in args.iter().enumerate() {
                        if lazy_mask.get(index).copied().unwrap_or(false) {
                            // Lazy: wrap in closure so the unevaluated expression
                            // is preserved for structural pattern matching
                            // (e.g., (== $A $B) or (eval $A)).
                            prebound_args.push(Some(plain(vec![
                                crate::eval::forms::query::delayed_user_call_arg(arg, env),
                            ])));
                        } else if let Some(atom) =
                            crate::eval::shared::closure::definition_arg_atom(arg, env)
                        {
                            // Preserve (= head body) or (quote ...) as data atom
                            prebound_args.push(Some(plain(vec![atom])));
                        } else {
                            prebound_args.push(None);
                            eager_indices.push(index);
                        }
                    }
                    work.push(Task::Apply(Frame::Call {
                        head: Head::User {
                            name: head.clone(),
                            clauses: clause_refs,
                            lazy_mask,
                        },
                        arity: args.len(),
                        env: env.clone(),
                        prebound_args: Some(prebound_args),
                    }));
                    for index in eager_indices.into_iter().rev() {
                        work.push(Task::Eval {
                            expr: Arc::new(args[index].clone()),
                            env: env.clone(),
                        });
                    }
                    return Ok(());
                }

                // Partial application: function exists at higher arity.
                if funcs.has_higher_arity(head, args.len()) {
                    let n_args = args.len();
                    work.push(Task::Apply(Frame::ApplyHead {
                        arity: n_args,
                        env: env.clone(),
                    }));
                    work.push(Task::Eval {
                        expr: Arc::new(items[0].clone()),
                        env: env.clone(),
                    });
                    for arg in args.iter().rev() {
                        work.push(Task::Eval {
                            expr: Arc::new(arg.clone()),
                            env: env.clone(),
                        });
                    }
                    return Ok(());
                }
            }

            // Head is a $var bound to a closure — apply it as a user function
            if let Expr::Symbol(head_sym) = &items[0] {
                if head_sym.starts_with('$') {
                    if let Some(crate::atom::Atom::Closure(c)) =
                        crate::eval::shared::env::lookup(env, head_sym.as_str())
                    {
                        let n_args = items.len() - 1;
                        let call_args = &items[1..];
                        work.push(Task::Apply(Frame::Call {
                            head: Head::User {
                                name: head_sym.clone(),
                                clauses: vec![(c.params.clone(), c.body.clone())],
                                lazy_mask: vec![false; n_args],
                            },
                            arity: n_args,
                            env: c.env.clone(),
                            prebound_args: None,
                        }));
                        for arg in call_args.iter().rev() {
                            work.push(Task::Eval {
                                expr: Arc::new(arg.clone()),
                                env: env.clone(),
                            });
                        }
                        return Ok(());
                    }
                }
            }

            // Compound head (e.g. inline lambda): evaluate head, apply as closure/function
            if !matches!(&items[0], Expr::Symbol(_)) {
                let n_args = items.len() - 1;
                work.push(Task::Apply(Frame::ApplyHead { arity: n_args, env: env.clone() }));
                // Push head FIRST, args in REVERSE order (head must execute AFTER args
                // so head result is on TOP of vals stack for ApplyHead to pop first)
                work.push(Task::Eval {
                    expr: Arc::new(items[0].clone()),
                    env: env.clone(),
                });
                for arg in items[1..].iter().rev() {
                    work.push(Task::Eval {
                        expr: Arc::new(arg.clone()),
                        env: env.clone(),
                    });
                }
                return Ok(());
            }

            work.push(Task::Apply(Frame::DataList { n: items.len() }));
            for item in items.iter().rev() {
                work.push(Task::Eval {
                    expr: Arc::new(item.clone()),
                    env: env.clone(),
                });
            }
            Ok(())
        }
    }
}
