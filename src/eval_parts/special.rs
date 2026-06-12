/// Special form evaluators.
///
/// Each function in this module evaluates one MeTTa special form:
/// control flow (`if`, `progn`, `let`, `let*`, `forall`, `case`, `chain`),
/// data constructors (`quote`, `repr`, `within`, `superpose`, `collapse`),
/// lambda (`|->`), and collection operations (`foldall`, `map-atom`,
/// `generate_free_var_values`).
///
/// # Naming convention
///
/// Every `eval_*` function shares the same basic signature:
/// `fn eval_NAME(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String>`
/// Some simpler forms (quote, repr, lambda) only need `(args, env)`.

use crate::atom::{Atom, ClosureData};
use crate::env::Env;
use crate::func::{Clause, FnTable, FunctionKind, NDet};
use crate::parser::{atom_to_expr, Expr};
use super::constrained::eval_constrained;
use super::core::{apply_closure, eval};
use super::pattern::{prepend_env, try_match_one};
use crate::trace;
use std::sync::Arc;

// ========================================================================
// Control flow
// ========================================================================

/// Evaluate `(if cond then else)`.
pub(crate) fn eval_if(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() < 2 || args.len() > 3 {
        return Err(format!(
            "if: expected 2 or 3 args, got {}",
            args.len()
        ));
    }
    // Use constraint-aware evaluation for the condition so free-variable bindings
    // (e.g. $x→True from clause matching) are threaded into the template.
    let mut out: Vec<Atom> = Vec::new();
    let mut had_bindings = false;
    for (cond, cond_bindings) in super::constrained::eval_constrained(&args[0], env, funcs)? {
        if !matches!(cond_bindings, crate::env::Env::Empty) {
            had_bindings = true;
        }
        if cond.is_truthy() {
            let then_env = super::pattern::prepend_env(cond_bindings, env);
            out.extend(super::core::eval(&args[1], &then_env, funcs)?);
        } else if let Some(else_expr) = args.get(2) {
            out.extend(super::core::eval(else_expr, env, funcs)?);
        }
        // 2-arg form: false condition contributes nothing
    }
    Ok(match out.len() {
        0 => NDet::stream(std::iter::empty()),
        1 => NDet::single(out.remove(0)),
        // Constraint-solving produced multiple solutions (bindings were non-empty):
        // collect into a single list atom so (test (if cond tmpl) ((s1) (s2))) works.
        // Non-det condition (superpose etc.) with empty bindings: stream results.
        _ if had_bindings => NDet::single(Atom::Expr(out)),
        _ => NDet::stream(out.into_iter()),
    })
}

/// Evaluate `(progn e1 e2 ...)` — sequence.
/// In PeTTa, `let` variables leak into the rest of the progn. We replicate this
/// by AST-rewriting the rest of the progn into the let body.
pub(crate) fn eval_progn(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.is_empty() {
        return Err("progn: expected at least one form".into());
    }

    let mut last: Option<NDet> = None;
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];

        // Rewrite (let pat val body) followed by e_rest...
        // into (let pat val (progn body e_rest...))
        if let Expr::List(items) = arg {
            if items.len() == 4 && items[0] == Expr::Symbol("let".to_string()) {
                if i + 1 < args.len() {
                    let pat = items[1].clone();
                    let val = items[2].clone();
                    let body = &items[3];
                    let mut new_progn_args = vec![body.clone()];
                    new_progn_args.extend_from_slice(&args[i+1..]);
                    let new_progn = Expr::List(
                        vec![Expr::Symbol("progn".to_string())]
                            .into_iter()
                            .chain(new_progn_args)
                            .collect()
                    );
                    let new_let = Expr::List(vec![
                        Expr::Symbol("let".to_string()),
                        pat,
                        val,
                        new_progn,
                    ]);
                    last = Some(super::core::eval(&new_let, env, funcs)?);
                    break; // The rest of the forms are now in the `let` body
                }
            } else if items.len() == 3 && items[0] == Expr::Symbol("let*".to_string()) {
                if i + 1 < args.len() {
                    let bindings = items[1].clone();
                    let body = &items[2];
                    let mut new_progn_args = vec![body.clone()];
                    new_progn_args.extend_from_slice(&args[i+1..]);
                    let new_progn = Expr::List(
                        vec![Expr::Symbol("progn".to_string())]
                            .into_iter()
                            .chain(new_progn_args)
                            .collect()
                    );
                    let new_let = Expr::List(vec![
                        Expr::Symbol("let*".to_string()),
                        bindings,
                        new_progn,
                    ]);
                    last = Some(super::core::eval(&new_let, env, funcs)?);
                    break;
                }
            } else if items.len() == 4 && items[0] == Expr::Symbol("match".to_string()) {
                // Wrap subsequent forms into a let block that binds the output of match.
                // e.g. (match space pat result) e_rest...
                // => (let result (match space pat result) (progn e_rest...))
                // But only if `result` acts as a pattern (usually just a variable like $x).
                if i + 1 < args.len() {
                    if let Expr::Symbol(s) = &items[3] {
                        if s.starts_with('$') {
                            let result_var = items[3].clone();
                            let mut new_progn_args = vec![];
                            new_progn_args.extend_from_slice(&args[i+1..]);
                            let new_progn = Expr::List(
                                vec![Expr::Symbol("progn".to_string())]
                                    .into_iter()
                                    .chain(new_progn_args)
                                    .collect()
                            );
                            let new_let = Expr::List(vec![
                                Expr::Symbol("let".to_string()),
                                result_var,
                                arg.clone(), // The match!
                                new_progn,
                            ]);
                            last = Some(super::core::eval(&new_let, env, funcs)?);
                            break;
                        }
                    }
                }
            }
        }

        last = Some(super::core::eval(arg, env, funcs)?);
        i += 1;
    }
    last.ok_or_else(|| "progn: internal — no forms after empty check".into())
}

/// Evaluate `(let pattern value body)` — nondeterministic pattern matching bind.
///
/// Evaluates `value` to produce a stream of atoms. For each atom, tries to
/// match `pattern` against it. On match, extends the environment with the
/// bindings and evaluates `body`. On mismatch, that branch produces no
/// results (empty stream contribution).
///
/// Pattern syntax (same as multi-clause `try_match_one`):
/// - `$var` — bind to value, or check equality if already bound by earlier
///   pattern elements (non-linear patterns)
/// - `Num(n)` — match only `Atom::Num(n)`
/// - `Sym(s)` — match only `Atom::Sym(s)` (non-`$` symbols are literal)
/// - `(pat1 pat2 ...)` — destructuring match against `Atom::Expr`
pub(crate) fn eval_let(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "let: expected (pattern value body), got {} args",
            args.len()
        ));
    }
    let pattern = &args[0];
    // PeTTa: translate_expr(Val, Gv, V) — always evaluate the value expression.
    let values: Vec<Atom> = super::core::eval(&args[1], env, funcs)?.collect();
    let streams: Vec<NDet> = values
        .into_iter()
        .filter_map(|v| {
            // Fresh match env prevents outer variable capture
            let match_env = super::pattern::try_match_one(pattern, &v, &Env::new(), funcs).ok()??;
            let new_env = super::pattern::prepend_env(match_env, env);
            // REASON: body eval failure in nondet stream is skipped,
            // not propagated — matches PeTTa's backtracking semantics.
            match super::core::eval(&args[2], &new_env, funcs) {
                Ok(res) => Some(res),
                Err(e) => {
                    eprintln!("DEBUG eval_let error: {}", e);
                    None
                }
            }
        })
        .collect();
    Ok(NDet::stream(streams.into_iter().flatten()))
}

/// Evaluate `(let* ((pat val) (pat2 val2) ...) body)` — sequential pattern let.
///
/// Evaluates each value in order. For each value, matches the corresponding
/// pattern using the same semantics as `try_match_one`. Later bindings see
/// variables bound by earlier patterns. If any pattern fails to match the
/// value, returns an error (deterministic binding).
pub(crate) fn eval_let_star(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "let*: expected ((bindings) body), got {} args",
            args.len()
        ));
    }
    let bindings = match &args[0] {
        Expr::List(items) => items,
        _ => {
            return Err(
                "let*: first arg must be a list of (pattern val) pairs".into(),
            )
        }
    };
    let mut current_env = env.clone();
    for pair in bindings {
        match pair {
            Expr::List(p) if p.len() == 2 => {
                let pattern = &p[0];
                // PeTTa: letstar_to_rec_let expands to nested let, which always evaluates.
                let mut val_results = super::core::eval(&p[1], &current_env, funcs)?;
                let val = val_results.next().ok_or_else(|| {
                    format!("let*: binding {} produced no value", pattern.to_string())
                })?;
                // Fresh match env prevents outer variable capture
                let match_env = super::pattern::try_match_one(pattern, &val, &Env::new(), funcs)?
                    .ok_or_else(|| {
                        format!("let*: pattern does not match value: {} vs {}",
                            pattern.to_string(), val.to_sexpr_string())
                    })?;
                current_env = super::pattern::prepend_env(match_env, &current_env);
            }
            _ => {
                return Err("let*: each binding must be a list (pattern val)".into())
            }
        }
    }
    super::core::eval(&args[1], &current_env, funcs)
}

// ========================================================================
// Data constructors / special expressions
// ========================================================================

/// Evaluate `(within expr)` — evaluate `expr` then wrap result in `(within ...)`.
///
/// PeTTa semantics: `within` is NOT a registered function; it's a data constructor
/// marker. Its argument is a regular MeTTa expression that IS evaluated (via `call`
/// semantics — i.e., normal evaluation), and the result is wrapped in `(within ...)`.
/// This is equivalent to `(= (within $x) (within $x))` evaluated in data-list context.
pub(crate) fn eval_within(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("within: expected 1 arg, got {}", args.len()));
    }
    let result_atom = match super::core::eval(&args[0], env, funcs) {
        Ok(nd) => {
            let vals: Vec<Atom> = nd.collect();
            if vals.is_empty() {
                return Err("within: expression produced no results".into());
            }
            if vals.len() > 1 {
                Atom::Expr(std::iter::once(Atom::sym("within")).chain(vals.into_iter()).collect())
            } else {
                Atom::Expr(vec![Atom::sym("within"), vals.into_iter().next().unwrap()])
            }
        }
        Err(e) => return Err(format!("within: {}", e)),
    };
    crate::trace!("within: {}", result_atom.to_sexpr_string());
    Ok(NDet::single(result_atom))
}

/// Evaluate `(quote expr)` — return expression as data, substituting bound `$vars`.
///
/// PeTTa: `Out = Expr` where Expr is the raw Prolog term. Bound Prolog variables
/// are already unified, so `(quote $x)` where $x=10 returns 10, not the symbol "$x".
/// We replicate this by substituting env-bound `$vars` before converting to atom.
pub(crate) fn eval_quote(args: &[Expr], env: &Env) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("quote: expected 1 arg, got {}", args.len()));
    }
    let atom = subst_and_atomize(&args[0], env);
    Ok(NDet::single(atom))
}

/// Evaluate `(repr expr)` — return the S-expression text of `expr` as a symbol.
/// Unlike `quote`, this does NOT substitute bound `$vars` — it returns the
/// literal source text so that `(repr (remove-all-atoms &self))` produces
/// the string `(remove-all-atoms &self)`.
pub(crate) fn eval_repr(args: &[Expr], _env: &Env) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("repr: expected 1 arg, got {}", args.len()));
    }
    Ok(NDet::single(Atom::sym(&args[0].to_string())))
}

/// Convert an `Expr` to an `Atom`, substituting bound `$vars` from `env`.
/// Unbound `$vars` are left as `Atom::Sym("$name")`.
pub(crate) fn subst_and_atomize(expr: &Expr, env: &Env) -> Atom {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            env.get(s).unwrap_or_else(|| Atom::sym(s))
        }
        Expr::List(items) => Atom::Expr(items.iter().map(|e| subst_and_atomize(e, env)).collect()),
        Expr::Number(n) => Atom::Num(*n),
        Expr::Symbol(s) => Atom::sym(s),
    }
}

/// Substitute bound variables in an Expr, keeping pattern structure intact.
/// Converts Atom values back to Expr for use in patterns.
pub(crate) fn subst_expr_vars(expr: &Expr, env: &Env) -> Expr {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            if let Some(atom) = env.get(s) {
                crate::parser::atom_to_expr(&atom).unwrap_or_else(|_| expr.clone())
            } else {
                expr.clone()
            }
        }
        Expr::List(items) => Expr::List(items.iter().map(|e| subst_expr_vars(e, env)).collect()),
        _ => expr.clone(),
    }
}

/// Evaluate `(|-> params body)` — lambda expression.
///
/// Creates a closure: captures the current lexical environment and stores
/// the parameter patterns and body expression. The closure is callable —
/// when applied, arguments are matched against params and body is evaluated
/// in the captured environment extended with the bindings.
pub(crate) fn eval_lambda(args: &[Expr], env: &Env) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "|->: expected (params body), got {} args", args.len()
        ));
    }
    let params = match &args[0] {
        Expr::List(items) => items.clone(),
        other => vec![other.clone()],
    };
    let closure = Atom::Closure(Box::new(ClosureData {
        params,
        body: args[1].clone(),
        env: env.clone(),
    }));
    Ok(NDet::single(closure))
}

// ========================================================================
// Quantification and iteration
// ========================================================================

/// Evaluate `(forall gen-expr check)` — universal quantification over NDet results.
///
/// Collects all results from `gen-expr`, applies `check` to each, returns
/// `true` if all pass (or generator is empty), `false` otherwise.
/// `check` can be a function name symbol or a closure.
pub(crate) fn eval_forall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!("forall: expected 2 args, got {}", args.len()));
    }
    // Use constrained eval for generator so free vars enumerate all clause solutions.
    let gen_values: Vec<Atom> = super::constrained::eval_constrained(&args[0], env, funcs)?
        .into_iter()
        .map(|(a, _)| a)
        .collect();
    let check = super::core::eval(&args[1], env, funcs)?
        .next()
        .ok_or_else(|| "forall: check produced no value".to_string())?;

    let arg_sym = Expr::Symbol("$__fv".to_string());
    for val in gen_values {
        let call_env = env.extend("$__fv", val);
        let results: Vec<Atom> = match &check {
            Atom::Sym(fname) => {
                let call = Expr::List(vec![Expr::Symbol(fname.to_string()), arg_sym.clone()]);
                super::core::eval(&call, &call_env, funcs)?.collect()
            }
            Atom::Closure(c) => {
                super::core::apply_closure(&c.params, &c.body, &c.env, &[arg_sym.clone()], &call_env, funcs)?
                    .collect()
            }
            other => return Err(format!(
                "forall: check must be a function or closure, got {}",
                other.to_sexpr_string()
            )),
        };
        if results.is_empty() || !results.iter().all(|a| a.is_truthy()) {
            return Ok(NDet::single(Atom::sym("false")));
        }
    }
    Ok(NDet::single(Atom::sym("true")))
}

// ========================================================================
// Call and re-evaluation
// ========================================================================

/// Evaluate `(call expr)` — evaluate the expression as a function call.
///
/// PeTTa semantics: translates to a direct predicate call at compile time.
/// In our runtime, this is equivalent to evaluating the single argument
/// as a normal expression (the dispatch loop handles function vs data).
///
/// `(reduce expr)` uses the same semantics — runtime dispatch evaluation.
pub(crate) fn eval_call(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("call: expected 1 arg, got {}", args.len()));
    }
    super::core::eval(&args[0], env, funcs)
}

/// Evaluate `(eval expr)` — re-evaluate a raw expression as code.
///
/// PeTTa: the translator emits `eval(RawArg, Out)` where RawArg is the
/// *untranslated* source term. `eval/2` then re-translates and runs it.
/// This means `(eval (quote (fib 5)))` returns `(fib 5)` as data (quote
/// stops the inner eval), not 5.
///
/// For a `$var`, the variable's atom value is treated as code and evaluated.
/// For any other literal expression, it is passed directly to eval.
pub(crate) fn eval_eval(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("eval: expected 1 arg, got {}", args.len()));
    }
    match &args[0] {
        Expr::Symbol(s) if s.starts_with('$') => {
            // $var: retrieve the atom it holds, convert to code, evaluate.
            let val = env
                .get(s)
                .ok_or_else(|| format!("eval: unbound variable {}", s))?;
            let expr = crate::parser::atom_to_expr(&val)?;
            super::core::eval(&expr, env, funcs)
        }
        // Literal expression: pass directly to eval — no pre-evaluation.
        _ => super::core::eval(&args[0], env, funcs),
    }
}

// ========================================================================
// Superpose and collapse
// ========================================================================

/// Evaluate `(superpose expr)` — spread elements of a list or atom into a stream.
///
/// PeTTa semantics: `superpose(L,X) :- member(X,L)`. Takes a single argument.
/// If the argument is a literal list `(a b c)`, evaluate each element and include
/// its full result stream. If the argument evaluates to an `Atom::Expr`, unpack
/// its elements. Otherwise return the atom as a single result.
pub(crate) fn eval_superpose(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err("superpose: expected exactly 1 argument (a list)".into());
    }
    let arg = &args[0];
    // Literal list: evaluate each element, produce their full streams
    if let Expr::List(items) = arg {
        let streams: Result<Vec<NDet>, String> = items
            .iter()
            .map(|e| super::core::eval(e, env, funcs))
            .collect();
        return Ok(NDet::stream(streams?.into_iter().flatten()));
    }
    // Non-list: evaluate, then unpack if Expr value
    let mut results = super::core::eval(arg, env, funcs)?;
    let val = results.next().ok_or_else(|| {
        "superpose: argument produced no results".to_string()
    })?;
    match val {
        Atom::Expr(elements) => Ok(NDet::stream(elements.into_iter())),
        other => Ok(NDet::single(other)),
    }
}

/// Evaluate `(collapse expr)` — collect all results into a list atom.
pub(crate) fn eval_collapse(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("collapse: expected 1 arg, got {}", args.len()));
    }
    let results: Vec<Atom> = super::core::eval(&args[0], env, funcs)?.collect();
    Ok(NDet::single(Atom::Expr(results)))
}

// ========================================================================
// foldall — fold over nondeterministic stream
// ========================================================================

/// Evaluate `(foldall agg-func gen-expr init)` — fold over a nondeterministic stream.
///
/// Collects all results from `gen-expr`, then folds them using `agg-func`:
/// `agg(agg(agg(init, v1), v2), v3) ...`. Returns the final accumulator.
///
/// When `gen-expr` contains unbound `$`-variables (e.g. `(g $x)` where `$x` is
/// free), the function attempts free-variable resolution: it finds each clause
/// of the generator's function and extracts literal values from the clause
/// patterns at the free-variable position, then calls the function with each
/// concrete value.
///
/// PeTTa reference: `foldall` aggregates over all solutions of a generator.
pub(crate) fn eval_foldall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "foldall: expected (agg-func gen-expr init), got {} args",
            args.len()
        ));
    }
    let agg_func = &args[0];
    // Collect all values from generator — try normal eval first, then
    // fall back to free-variable resolution if the expression has unbound vars.
    let gen_values: Vec<Atom> = match super::core::eval(&args[1], env, funcs) {
        Ok(results) => results.collect(),
        Err(_) => generate_free_var_values(&args[1], env, funcs)?,
    };
    // Evaluate init value (first result)
    let mut init_results = super::core::eval(&args[2], env, funcs)?;
    let init = init_results.next().ok_or_else(|| {
        "foldall: init expression produced no results".to_string()
    })?;
    // Fold: accum = agg(accum, next) for each gen value
    let accum = gen_values.into_iter().try_fold(init, |acc, val| {
        let acc_expr = crate::parser::atom_to_expr(&acc)?;
        let val_expr = crate::parser::atom_to_expr(&val)?;
        let call = Expr::List(vec![agg_func.clone(), acc_expr, val_expr]);
        let mut results = super::core::eval(&call, env, funcs)?;
        results.next().ok_or_else(|| {
            "foldall: aggregate function produced no results".to_string()
        })
    })?;
    Ok(NDet::single(accum))
}

/// Try to generate values from a function call expression with free variables.
///
/// When a generator like `(g $x)` contains an unbound `$x`, this function
/// looks up `g` in the function table, iterates over its clauses, and for
/// each clause extracts the literal value at the free-variable position.
/// It then calls `g` with each literal value and collects the results.
///
/// Currently only handles the single-free-variable case with literal (number
/// or symbol) patterns. Nested patterns or multiple free variables are not
/// supported and return an error.
pub(crate) fn generate_free_var_values(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    let items = match expr {
        Expr::List(items) if !items.is_empty() => items,
        _ => return Err(format!(
            "generator: expected a function call, got {}", expr.to_string()
        )),
    };
    let op = &items[0];
    let arity = items.len() - 1;
    // Evaluate the operator to get the function name
    let op_atom = match super::core::eval(op, env, funcs)?.next() {
        Some(a) => a,
        None => return Err("generator: operator produced no results".into()),
    };
    // Closure generator: (closure arg...) — bind params to concrete args (if any),
    // then eval or recurse on the body with the remaining free variables.
    if let Atom::Closure(c) = &op_atom {
        let (params, body, capture_env) = (&c.params, &c.body, &c.env);
        let mut closure_env = capture_env.clone();
        for (param, arg_expr) in params.iter().zip(items[1..].iter()) {
            let is_free = matches!(arg_expr, Expr::Symbol(s) if s.starts_with('$') && env.get(s).is_none());
            if !is_free {
                if let Ok(mut evaled) = super::core::eval(arg_expr, env, funcs) {
                    if let Some(val) = evaled.next() {
                        if let Expr::Symbol(pname) = param {
                            closure_env = closure_env.extend(pname, val);
                        }
                    }
                }
            }
        }
        let body_results: Vec<Atom> = match super::core::eval(body, &closure_env, funcs) {
            Ok(r) => r.collect(),
            Err(_) => generate_free_var_values(body, &closure_env, funcs)?,
        };
        return Ok(body_results);
    }
    let fname = match &op_atom {
        Atom::Sym(s) => s.clone(),
        _ => return Err(format!(
            "generator: expected function name, got {}", op_atom.to_sexpr_string()
        )),
    };
    // SAFETY: arity = items.len() - 1; items is non-empty (guarded above), so arity < 256.
    let func_ref = funcs.get(&fname, arity as u8).ok_or_else(|| {
        format!("generator: unknown function {} with {} args", fname, arity)
    })?;
    let is_native = matches!(&func_ref.kind, FunctionKind::Native { .. });
    let (clauses, native_func): (Vec<Clause>, Option<Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>>) = match &func_ref.kind {
        FunctionKind::UserDefined { clauses } => (clauses.clone(), None),
        FunctionKind::Native { func: f } => (vec![], Some(Arc::clone(f))),
    };
    drop(func_ref);
    if is_native {
        if let Some(f) = native_func {
            // For each arg, collect all possible values:
            // concrete args → one value; free-var args → recurse to get many values.
            // Then call the native with every combination (cartesian product).
            let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(arity);
            for arg_expr in &items[1..] {
                match super::core::eval(arg_expr, env, funcs) {
                    Ok(nd) => {
                        let vals: Vec<Atom> = nd.collect();
                        if vals.is_empty() { return Ok(vec![]); }
                        arg_options.push(vals);
                    }
                    Err(_) => {
                        // eval failed — treat as free variable generation
                        let opts = generate_free_var_values(arg_expr, env, funcs)?;
                        arg_options.push(opts);
                    }
                }
            }
            // Cartesian product
            let mut results = Vec::new();
            let mut indices = vec![0usize; arg_options.len()];
            loop {
                let args_slice: Vec<Atom> = indices.iter().enumerate()
                    .map(|(i, &idx)| arg_options[i][idx].clone())
                    .collect();
                if let Ok(mut nd) = f(&args_slice, funcs) {
                    while let Some(a) = nd.next() {
                        results.push(a);
                    }
                }
                // Increment indices
                let mut i = indices.len();
                while i > 0 {
                    i -= 1;
                    indices[i] += 1;
                    if indices[i] < arg_options[i].len() {
                        break;
                    }
                    indices[i] = 0;
                    if i == 0 { return Ok(results); }
                }
            }
        }
        return Err("generator: unexpected native dispatch failure".into());
    }
    // UserDefined
    let mut results = Vec::new();
    for clause in &clauses {
        if clause.patterns.len() != arity {
            continue;
        }
        let mut concrete_args = Vec::with_capacity(arity);
        let mut has_free = false;
        for (i, arg_expr) in items[1..].iter().enumerate() {
            if let Expr::Symbol(s) = arg_expr {
                if s.starts_with('$') && env.get(s).is_none() {
                    match &clause.patterns[i] {
                        Expr::Number(n) => {
                            concrete_args.push(Atom::Num(*n));
                            has_free = true;
                        }
                        Expr::Symbol(sym) if !sym.starts_with('$') => {
                            concrete_args.push(Atom::sym(&sym));
                            has_free = true;
                        }
                        _ => {
                            concrete_args.clear();
                            break;
                        }
                    }
                    continue;
                }
            }
            // Normal evaluation
            let mut evaled = super::core::eval(arg_expr, env, funcs)?;
            match evaled.next() {
                Some(a) => concrete_args.push(a),
                None => { concrete_args.clear(); break; }
            }
        }
        if !has_free || concrete_args.len() != arity {
            continue;
        }
        let mut matched = true;
        let mut match_env = Env::new();
        for (pat, arg_val) in clause.patterns.iter().zip(concrete_args.iter()) {
            match super::pattern::try_match_one(pat, arg_val, &match_env, funcs)? {
                Some(new_env) => match_env = new_env,
                None => { matched = false; break; }
            }
        }
        if !matched {
            continue;
        }
        let new_env = super::pattern::prepend_env(match_env, env);
        let mut body_results = super::core::eval(&clause.body, &new_env, funcs)?;
        while let Some(atom) = body_results.next() {
            results.push(atom);
        }
    }
    if results.is_empty() {
        return Err(format!(
            "generator: {}: no clauses with literal patterns for free variables",
            fname
        ));
    }
    Ok(results)
}

// ========================================================================
// map-atom — map over list elements
// ========================================================================

/// Evaluate `(map-atom list func)` — apply `func` to each element of `list`.
///
/// PeTTa runtime: `'map-atom'([H|T], Func, [R|RT]) :- reduce([Func,H], R)`.
/// `reduce/2` dispatches on Func type:
///   - registered atom → direct call
///   - closure         -> apply_closure
///   - anything else   → produce `[Func, H]` as data (no error)
pub(crate) fn eval_map_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "map-atom: expected (list func), got {} args",
            args.len()
        ));
    }
    let mut list_results = super::core::eval(&args[0], env, funcs)?;
    let list_atom = list_results.next().ok_or_else(|| {
        "map-atom: list expression produced no results".to_string()
    })?;
    let mut func_results = super::core::eval(&args[1], env, funcs)?;
    let func_atom = func_results.next().ok_or_else(|| {
        "map-atom: func expression produced no results".to_string()
    })?;
    // Move elements out — list_atom not needed after this.
    let elements = match list_atom {
        Atom::Expr(items) => items,
        other => return Err(format!(
            "map-atom: expected a list (Expr), got {}",
            other.to_sexpr_string()
        )),
    };
    let mut results = Vec::with_capacity(elements.len());
    for elem in &elements {
        // reduce([Func, H], R) dispatch:
        let result = match &func_atom {
            Atom::Sym(fname) => {
                let elem_expr = crate::parser::atom_to_expr(elem)?;
                let call_expr = Expr::List(vec![Expr::Symbol(fname.to_string()), elem_expr]);
                let mut r = super::core::eval(&call_expr, env, funcs)?;
                r.next().ok_or_else(|| format!(
                    "map-atom: {} returned no result for {}",
                    fname, elem.to_sexpr_string()
                ))?
            }
            Atom::Closure(c) => {
                let elem_expr = crate::parser::atom_to_expr(elem)?;
                let mut r = super::core::apply_closure(&c.params, &c.body, &c.env, &[elem_expr], env, funcs)?;
                r.next().ok_or_else(|| format!(
                    "map-atom: closure returned no result for {}",
                    elem.to_sexpr_string()
                ))?
            }
            // reduce case 3: unknown func → [Func, H] as data
            _ => Atom::Expr(vec![func_atom.clone(), elem.clone()]),
        };
        results.push(result);
    }
    Ok(NDet::single(Atom::Expr(results)))
}

// ========================================================================
// chain — pipeline with intermediate bindings
// ========================================================================

/// Evaluate `(chain expr $var expr $var ... final-expr)` — thread value through
/// a pipeline of expressions.
///
/// Each expression is evaluated in order; its first result is bound to the
/// following `$var`, making it available to subsequent expressions. The final
/// expression's result is the overall result.
///
/// PeTTa reference: `chain(Value, Var, Expr, ...)` compiles to
/// `substitute(Value, Var, Expr, ChainResult)`.
///
/// # Errors
/// Returns error if any `$var` position is not a `$`-prefixed symbol, if any
/// expression produces no results, or if arg count is even.
pub(crate) fn eval_chain(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() == 1 {
        // Single expression: evaluate and return directly
        return super::core::eval(&args[0], env, funcs);
    }
    if args.len() < 3 || args.len() % 2 == 0 {
        return Err(format!(
            "chain: expected odd number of args (expr $var expr ...), got {}",
            args.len()
        ));
    }
    let mut current_env = env.clone();
    let last_idx = args.len() - 1;

    // Process (expr, $var) pairs up to the last expression
    let pairs = args.len() / 2; // integer division
    for i in 0..pairs {
        let expr = &args[i * 2];
        let var = &args[i * 2 + 1];

        // Var must be a $variable
        let var_name = match var {
            Expr::Symbol(s) if s.starts_with('$') => s.clone(),
            _ => return Err(format!(
                "chain: arg {} must be a $variable, got {}",
                i * 2 + 1, var.to_string()
            )),
        };

        // Evaluate expression, take first result
        let mut results = super::core::eval(expr, &current_env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("chain: expression {} produced no results", i * 2)
        })?;

        current_env = current_env.extend(&var_name, val);
    }

    // Evaluate final expression
    super::core::eval(&args[last_idx], &current_env, funcs)
}

// ========================================================================
// case — pattern match dispatch
// ========================================================================

/// Evaluate `(case expr (pattern1 body1) (pattern2 body2) ...)` — pattern match dispatch.
///
/// Evaluates `expr`, takes the first result, then tries each clause's pattern
/// against it (in order). The first matching clause's body is evaluated with
/// the matched bindings. `$else` always matches as a catch-all.
///
/// PeTTa reference: `case(Value, PatternBodyPairs)` compiles to
/// match-then-evaluate over the list of (pattern, body) pairs.
///
/// # Errors
/// Returns error if no clause matches the value.
/// Try one (value, clauses) combination for case: find first matching clause
/// and evaluate its body. Returns the body results or an error.
pub(crate) fn try_case_value(val: &Atom, clauses: &[Expr], env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    for clause in clauses {
        let (pattern, body) = match clause {
            Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
            _ => return Err(format!(
                "case: each clause must be (pattern body), got {}",
                clause.to_string()
            )),
        };
        if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
            continue;
        }
        if matches!(pattern, Expr::Symbol(s) if s == "$else") {
            return super::core::eval(body, env, funcs).map(|r| r.collect());
        }
        if let Some(match_env) = super::pattern::try_match_one(pattern, val, &Env::new(), funcs)? {
            let new_env = super::pattern::prepend_env(match_env, env);
            return super::core::eval(body, &new_env, funcs).map(|r| r.collect());
        }
    }
    Err(format!(
        "case: no clause matched value {}", val.to_sexpr_string()
    ))
}

/// Evaluate `(case expr (pattern1 body1) (pattern2 body2) ...)` — pattern match dispatch.
pub(crate) fn eval_case(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "case: expected (expr (clauses...)), got {} args",
            args.len()
        ));
    }

    // Get clauses list up front
    let clauses = match &args[1] {
        Expr::List(items) => items,
        _ => return Err("case: second arg must be a list of (pattern body) pairs".into()),
    };

    // Collect all scrutinee values (may be nondeterministic)
    let vals: Vec<Atom> = super::core::eval(&args[0], env, funcs)?.collect();

    // Empty scrutinee: look for (Empty body) clause
    if vals.is_empty() {
        for clause in clauses {
            let (pattern, body) = match clause {
                Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
                _ => continue,
            };
            if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
                return super::core::eval(body, env, funcs);
            }
        }
        return Ok(NDet::stream(std::iter::empty()));
    }

    // Parallel fan-out: for each scrutinee value, match clauses independently.
    // The inner loop (per-value clause matching) stays sequential to preserve
    // first-match-wins semantics. Different values are independent.
    let results: Vec<Result<Vec<Atom>, String>> = if vals.len() > 1 {
        use rayon::prelude::*;
        vals.par_iter().map(|val| try_case_value(val, clauses, env, funcs)).collect()
    } else {
        vals.iter().map(|val| try_case_value(val, clauses, env, funcs)).collect()
    };
    let mut out: Vec<Atom> = Vec::new();
    for r in results {
        out.extend(r?);
    }
    Ok(NDet::stream(out.into_iter()))
}
