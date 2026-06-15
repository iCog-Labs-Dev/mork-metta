//! Explicit-stack CEK evaluation machine (iterative replacement for the
//! recursive tree-walk `eval`).
//!
//! # Why
//!
//! The recursive evaluator (`core::eval`) blows the native Rust stack on deep
//! MeTTa recursion (fib, Peano), because the unbounded recursion depth flows
//! through an *interleaved* spine: `eval` → arg/body eval → special forms →
//! `eval`. The current mitigation is 32MB stacks on every rayon worker
//! (`main.rs`), which causes a large page-zeroing / allocation perf regression.
//!
//! This module reifies the call stack onto the heap. Evaluation becomes a loop
//! over two stacks — `work: Vec<Task>` (what to evaluate) and `vals:
//! Vec<ResultSet>` (results flowing up to continuation frames). MeTTa recursion
//! depth then grows the heap, not the native stack, so default (2MB) thread
//! stacks suffice and the 32MB workaround can be removed.
//!
//! This mirrors the Meta-MeTTa spec's iterative register machine (§3.3) and the
//! reference Hyperon "interpretation plan" model.
//!
//! # Non-determinism
//!
//! Result-sets are **eager** `Vec<(Atom, Env)>` (the same shape as
//! `constrained::eval_constrained`), not lazy `NDet` streams. This matches the
//! existing `.collect()`-heavy code. Trade-off (accepted): `once` no longer
//! short-circuits and infinite/unbounded non-deterministic streams are not
//! supported. All bundled examples + tests are finite.
//!
//! # Rollout
//!
//! Phase 0 (this commit): scaffold + engine switch + differential-test harness.
//! `run_as_ndet` delegates to the recursive `eval` so behavior is identical and
//! the harness infrastructure is established. Later phases replace the body with
//! the real step loop.

use std::sync::atomic::{AtomicI64, AtomicU8, Ordering};
use std::sync::Arc;

use crate::atom::{Atom, ClosureData};
use crate::env::Env;
use crate::eval_parts::constrained::{cartesian_product, eval_constrained};
use crate::eval_parts::special::{generate_free_var_values, subst_and_atomize};
use crate::func::{FnTable, FunctionKind, NDet};
use crate::parser::{atom_to_expr, Expr};

/// A fully-reduced non-deterministic result multiset, with the bindings each
/// result carries (free-variable solutions threaded by `if`/`forall`, etc.).
///
/// Phase 1: the binding component is always `Env::Empty` for spine results;
/// constraint-binding threading lands with `if`/`forall` in Phase 3.
pub(crate) type ResultSet = Vec<(Atom, Env)>;

/// Wrap plain atoms (no constraint bindings) as a result-set.
fn plain(atoms: Vec<Atom>) -> ResultSet {
    atoms.into_iter().map(|a| (a, Env::Empty)).collect()
}

/// Strip bindings from a result-set, keeping only the result atoms in order.
fn atoms_of(rs: &ResultSet) -> Vec<Atom> {
    rs.iter().map(|(a, _)| a.clone()).collect()
}

// ========================================================================
// Engine selection
// ========================================================================

/// Which evaluation engine `eval_scope` (and `eval_with_state`) dispatch to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Engine {
    /// The original recursive tree-walk (`core::eval`).
    Recursive,
    /// The iterative explicit-stack CEK machine (this module).
    Cek,
}

const ENGINE_RECURSIVE: u8 = 0;
const ENGINE_CEK: u8 = 1;

/// Global engine selector. Global (not thread-local) on purpose: a single
/// evaluation may fan out onto rayon workers, and every worker must agree on
/// the engine. Defaults to the iterative `Cek` machine (explicit heap stack, no
/// native-stack-depth dependence); override with `METTA_EVAL=recursive`.
static ENGINE: AtomicU8 = AtomicU8::new(ENGINE_CEK);

/// Initialize the engine from the `METTA_EVAL` env var (call once at startup).
/// Unknown / unset → leaves the current default (`Cek`).
pub fn init_engine_from_env() {
    if let Ok(v) = std::env::var("METTA_EVAL") {
        match v.trim().to_ascii_lowercase().as_str() {
            "cek" => set_engine(Engine::Cek),
            "recursive" | "rec" => set_engine(Engine::Recursive),
            _ => {}
        }
    }
}

/// Read the active engine.
pub fn current_engine() -> Engine {
    match ENGINE.load(Ordering::Relaxed) {
        ENGINE_CEK => Engine::Cek,
        _ => Engine::Recursive,
    }
}

/// Set the active engine. Used by the differential-test harness and `main`.
pub fn set_engine(engine: Engine) {
    let v = match engine {
        Engine::Recursive => ENGINE_RECURSIVE,
        Engine::Cek => ENGINE_CEK,
    };
    ENGINE.store(v, Ordering::Relaxed);
}

/// Run `f` with `engine` active, restoring the previous engine afterwards.
/// Not re-entrancy-safe across threads (the flag is global); intended for the
/// single-threaded differential harness.
pub fn with_engine<R>(engine: Engine, f: impl FnOnce() -> R) -> R {
    let prev = current_engine();
    set_engine(engine);
    let r = f();
    set_engine(prev);
    r
}

// ========================================================================
// Entry point
// ========================================================================

/// Evaluate `expr` to a non-deterministic result stream using the CEK machine.
///
/// Phase 0: delegates to the recursive evaluator so output is identical while
/// the engine switch and differential harness are established. The real
/// explicit-stack loop lands in Phase 1.
pub fn run_as_ndet(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let results = run(expr, env, funcs)?;
    Ok(NDet::stream(results.into_iter()))
}

/// Evaluate `expr` to an eager ordered result multiset via the explicit-stack
/// step loop.
pub(crate) fn run(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    let mut budget = None;
    let rs = run_rs(Arc::new(expr.clone()), env.clone(), funcs, &mut budget)?;
    Ok(atoms_of(&rs))
}

/// Like [`run`], but resource-bounded: each user-function reduction (the spec's
/// Query/Chain step) deducts its cost `Σ#(uᵢσᵢ)` from `budget`; when the budget
/// would be exhausted the reduction halts early and returns the partial result
/// multiset. `budget == None` is unbounded (identical to [`run`]).
pub(crate) fn run_budgeted(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<Vec<Atom>, String> {
    let rs = run_rs(Arc::new(expr.clone()), env.clone(), funcs, budget)?;
    Ok(atoms_of(&rs))
}

// ========================================================================
// The machine
// ========================================================================

/// A unit of pending work on the heap work-stack.
enum Task {
    /// Reduce an expression in an environment.
    Eval { expr: Arc<Expr>, env: Env },
    /// A continuation: pop its child result-sets from the value stack and combine.
    Apply(Frame),
    /// Evaluate N independent (pure) sub-expressions in parallel via rayon,
    /// then combine. The sub-results are pushed to `vals` in task order before
    /// the continuation frame fires.
    ParEval {
        tasks: Vec<(Arc<Expr>, Env)>,
        frame: Box<Frame>,
    },
}

enum Head {
    /// A native (grounded) Rust builtin.
    Native(Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>),
    /// A user-defined function: its `(patterns, body)` clauses from cache/space.
    User {
        name: String,
        clauses: Vec<(Vec<Expr>, Expr)>,
    },
}

/// A continuation frame — the reified `K[·]` context.
enum Frame {
    /// After the call's N args are evaluated: cartesian-product, then dispatch
    /// to the native builtin or user-function clause matching.
    Call {
        head: Head,
        arity: usize,
        env: Env,
        /// Original list items, for the data-list fallback (empty-arg case).
        all_items: Arc<Vec<Expr>>,
    },
    /// Evaluate a list as data: cartesian over the N element result-sets,
    /// each combo wrapped in one `Atom::Expr`.
    DataList { n: usize },
    /// Data list with a pre-evaluated head atom (from compound-head dispatch).
    /// Only the N tail items are evaluated as tasks; the head value is already
    /// known. Mirrors `eval_data_list_with_head` to prevent double-evaluating
    /// the head expression.
    DataListWithHead { head: Atom, n_tail: usize },
    /// Concatenate N child result-sets in order (multi-clause / multi-combo
    /// body results).
    Gather { n: usize },
    /// `if`: branch result-sets already evaluated; apply the `eval_if` bundling
    /// rule (single Expr when constraint bindings were present and >1 result).
    IfGather { had_bindings: bool, n: usize },
    /// `within`: wrap the sub-expr's result(s) in `(within ...)`.
    WithinWrap,
    /// `collapse`: collect all sub-results into one `Atom::Expr`.
    CollapseGather,
    /// `once`: keep the first sub-result, drop the rest.
    OnceCut,
    /// `superpose` non-list: unpack the first result if it is an `Atom::Expr`.
    SuperposeUnpack,
    /// `let`: value result-set evaluated; match the pattern per value and push
    /// the body as a task for each match (body recursion stays iterative).
    LetMatch {
        pattern: Expr,
        body: Arc<Expr>,
        env: Env,
    },
}

/// Run the step loop to completion, returning the final result-set. `budget`, if
/// `Some`, is debited by user-function reductions (spec Query/Chain cost);
/// reduction halts once it is exhausted. Internally converted to `AtomicI64` so
/// that parallel sub-evaluations (`Task::ParEval`) share the budget safely.
fn run_rs(
    root: Arc<Expr>,
    root_env: Env,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<ResultSet, String> {
    let atomic_budget = Arc::new(match budget {
        Some(b) => AtomicI64::new(*b),
        None => AtomicI64::new(-1),
    });

    let mut work: Vec<Task> = vec![Task::Eval {
        expr: root,
        env: root_env,
    }];
    let mut vals: Vec<ResultSet> = Vec::new();

    while let Some(task) = work.pop() {
        match task {
            Task::Eval { expr, env } => dispatch(&expr, &env, funcs, &mut work, &mut vals)?,
            Task::Apply(frame) => combine(frame, funcs, &mut work, &mut vals, &atomic_budget)?,
            Task::ParEval { tasks, frame } => {
                let results = eval_par(&tasks, funcs, &atomic_budget)?;
                for rs in results {
                    vals.push(rs);
                }
                work.push(Task::Apply(*frame));
            }
        }
    }

    // Sync the atomic budget back to the caller's `&mut Option<i64>`.
    if let Some(b) = budget {
        let remaining = atomic_budget.load(Ordering::Acquire);
        if remaining >= 0 {
            *b = remaining;
        }
    }

    debug_assert_eq!(
        vals.len(),
        1,
        "machine ended with {} result-sets",
        vals.len()
    );
    Ok(vals.pop().unwrap_or_default())
}

/// Reduce one `Eval` task: either push a finished result-set, or push a frame
/// plus child `Eval` tasks (children pushed in REVERSE so the leftmost pops
/// first and the frame pops last).
fn dispatch(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    match expr {
        Expr::Number(n) => {
            vals.push(plain(vec![Atom::Num(*n)]));
            Ok(())
        }
        Expr::Symbol(s) => {
            let atom = if s.starts_with('$') {
                env.get(s).unwrap_or_else(|| Atom::sym(s))
            } else {
                Atom::sym(s)
            };
            vals.push(plain(vec![atom]));
            Ok(())
        }
        Expr::List(items) => {
            if items.is_empty() {
                vals.push(plain(vec![Atom::Expr(vec![])]));
                return Ok(());
            }
            let op = &items[0];

            // Special forms (operator NOT evaluated).
            if let Expr::Symbol(s) = op {
                let args = &items[1..];
                match s.as_str() {
                    "if" => return dispatch_if(args, env, funcs, work, vals),

                    // --- pure data constructors (no sub-eval) ---
                    "quote" => {
                        if args.len() != 1 {
                            return Err(format!("quote: expected 1 arg, got {}", args.len()));
                        }
                        vals.push(plain(vec![subst_and_atomize(&args[0], env)]));
                        return Ok(());
                    }
                    "repr" => {
                        if args.len() != 1 {
                            return Err(format!("repr: expected 1 arg, got {}", args.len()));
                        }
                        vals.push(plain(vec![Atom::sym(&args[0].to_string())]));
                        return Ok(());
                    }
                    "|->" => {
                        if args.len() != 2 {
                            return Err(format!(
                                "|->: expected (params body), got {} args",
                                args.len()
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
                        vals.push(plain(vec![closure]));
                        return Ok(());
                    }
                    "empty" => {
                        vals.push(Vec::new());
                        return Ok(());
                    }

                    // --- forms with one sub-eval + a combine frame ---
                    "within" => return push_unary(args, env, work, Frame::WithinWrap, "within"),
                    "collapse" => {
                        return push_unary(args, env, work, Frame::CollapseGather, "collapse");
                    }
                    "once" => return push_unary(args, env, work, Frame::OnceCut, "once"),

                    // --- pass-through (result is the sub-expr's result) ---
                    "call" | "reduce" => {
                        if args.len() != 1 {
                            return Err(format!("{}: expected 1 arg, got {}", s, args.len()));
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
                                (atom_to_expr(&val)?, env.clone())
                            }
                            other => (other.clone(), env.clone()),
                        };
                        work.push(Task::Eval {
                            expr: Arc::new(target),
                            env: tenv,
                        });
                        return Ok(());
                    }

                    // --- superpose ---
                    "superpose" => {
                        if args.len() != 1 {
                            return Err("superpose: expected exactly 1 argument (a list)".into());
                        }
                        match &args[0] {
                            // Literal list: eval each element, concatenate streams.
                            Expr::List(elems) => {
                                work.push(Task::Apply(Frame::Gather { n: elems.len() }));
                                for e in elems.iter().rev() {
                                    work.push(Task::Eval {
                                        expr: Arc::new(e.clone()),
                                        env: env.clone(),
                                    });
                                }
                            }
                            // Non-list: eval, then unpack first Expr result.
                            other => {
                                work.push(Task::Apply(Frame::SuperposeUnpack));
                                work.push(Task::Eval {
                                    expr: Arc::new(other.clone()),
                                    env: env.clone(),
                                });
                            }
                        }
                        return Ok(());
                    }

                    // --- let: body eval stays a task (iterative) ---
                    "let" => {
                        if args.len() != 3 {
                            return Err(format!(
                                "let: expected (pattern value body), got {} args",
                                args.len()
                            ));
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

                    // --- let*: bind sequentially (eager, first-result), body is a task ---
                    "let*" => {
                        // args[0] = ((pat val)...) bindings, args[1] = body.
                        let body_env = cek_let_star_env(args, env, funcs)?;
                        work.push(Task::Eval {
                            expr: Arc::new(args[1].clone()),
                            env: body_env,
                        });
                        return Ok(());
                    }

                    // --- chain: thread (expr $var) pairs eagerly, final is a task ---
                    "chain" => {
                        if args.len() == 1 {
                            work.push(Task::Eval {
                                expr: Arc::new(args[0].clone()),
                                env: env.clone(),
                            });
                            return Ok(());
                        }
                        let (final_expr, final_env) = cek_chain_env(args, env, funcs)?;
                        work.push(Task::Eval {
                            expr: final_expr,
                            env: final_env,
                        });
                        return Ok(());
                    }

                    // --- progn: AST-rewrite for let-leak, last form is a task ---
                    "progn" => return cek_progn(args, env, funcs, work),

                    // --- case: bodies are tasks (iterative) ---
                    "case" => return cek_case(args, env, funcs, work, vals),

                    // --- aggregations: eval_sub-based ---
                    "foldall" => {
                        vals.push(cek_foldall(args, env, funcs)?);
                        return Ok(());
                    }
                    "map-atom" => {
                        vals.push(cek_map_atom(args, env, funcs)?);
                        return Ok(());
                    }
                    "forall" => {
                        vals.push(cek_forall(args, env, funcs)?);
                        return Ok(());
                    }

                    // IO / space forms: delegate to their recursive evaluators
                    // (no deep recursion through them; revisited in Phase 4).
                    _ if is_special_form(s) => {
                        let nd = crate::eval_parts::core::eval(expr, env, funcs)?;
                        vals.push(plain(nd.collect()));
                        return Ok(());
                    }
                    _ => {}
                }
            }

            // Relational query: a call / data list containing an UNBOUND free
            // variable needs left-to-right binding propagation (Prolog-style) so
            // sibling args and data-list elements see each other's unifications.
            // Route to the constrained evaluator. Ground expressions (e.g. fib's
            // `(+ (fib (- $N 1)) ...)` where $N is bound) skip this and stay on
            // the fast iterative spine, preserving deep-recursion support.
            if expr_has_unbound_var(expr, env) {
                vals.push(eval_constrained(expr, env, funcs)?);
                return Ok(());
            }

            // Function call or data list.
            match op {
                Expr::Symbol(s) if !s.starts_with('$') => {
                    dispatch_call(s, &items[1..], items, env, funcs, work)
                }
                Expr::Symbol(s) => {
                    // $var-headed call: resolve the variable, then dispatch.
                    let op_val = env.get(s).unwrap_or_else(|| Atom::sym(s));
                    dispatch_resolved_head(op_val, &items[1..], items, env, funcs, work, vals)
                }
                _ => {
                    // Compound-headed call: evaluate the operator (first result),
                    // then dispatch on the resulting atom.
                    let op_rs = eval_sub(op, env, funcs)?;
                    let first = op_rs.into_iter().next().map(|(a, _)| a);
                    match first {
                        Some(head) => {
                            dispatch_resolved_head(head, &items[1..], items, env, funcs, work, vals)
                        }
                        None => {
                            // Operator produced nothing → whole list as data.
                            dispatch_data_list(items, env, work);
                            Ok(())
                        }
                    }
                }
            }
        }
    }
}

fn dispatch_call(
    name: &str,
    args: &[Expr],
    all_items: &[Expr],
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
) -> Result<(), String> {
    let arity = args.len() as u8;

    let head = if let Some(func) = funcs.get(name, arity) {
        match &func.kind {
            FunctionKind::Native { func: f } => Some(Head::Native(Arc::clone(f))),
        }
    } else if let Some(clauses) = lookup_user_clauses(name, arity, funcs) {
        Some(Head::User {
            name: name.to_string(),
            clauses,
        })
    } else {
        None
    };

    let all_items_arc = Arc::new(all_items.to_vec());
    match head {
        Some(head) => {
            let frame = Frame::Call {
                head,
                arity: args.len(),
                env: env.clone(),
                all_items: Arc::clone(&all_items_arc),
            };
            let parallel = crate::eval_parts::data_list::worth_parallel(args)
                && args
                    .iter()
                    .all(|a| crate::eval_parts::data_list::is_pure_expr(a, funcs));
            if parallel {
                let tasks: Vec<(Arc<Expr>, Env)> = args
                    .iter()
                    .cloned()
                    .map(Arc::new)
                    .map(|expr| (expr, env.clone()))
                    .collect();
                work.push(Task::ParEval {
                    tasks,
                    frame: Box::new(frame),
                });
            } else {
                work.push(Task::Apply(frame));
                for arg in args.iter().rev() {
                    work.push(Task::Eval {
                        expr: Arc::new(arg.clone()),
                        env: env.clone(),
                    });
                }
            }
            Ok(())
        }
        None => {
            dispatch_data_list(&all_items_arc, env, work);
            Ok(())
        }
    }
}

/// `(if cond then [else])`: evaluate the (shallow) condition eagerly via
/// constrained eval, then push the chosen branch(es) as `Eval` tasks so the
/// deep branch recursion runs iteratively.
fn dispatch_if(
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    if args.len() < 2 || args.len() > 3 {
        return Err(format!("if: expected 2 or 3 args, got {}", args.len()));
    }

    // Collect (branch_expr, branch_env) per condition solution, in order.
    let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
    let mut had_bindings = false;
    for (cond, cond_bindings) in eval_constrained(&args[0], env, funcs)? {
        if !matches!(cond_bindings, Env::Empty) {
            had_bindings = true;
        }
        if cond.is_truthy() {
            let then_env = crate::eval_parts::pattern::prepend_env(cond_bindings, env);
            branches.push((Arc::new(args[1].clone()), then_env));
        } else if let Some(else_expr) = args.get(2) {
            branches.push((Arc::new(else_expr.clone()), env.clone()));
        }
        // 2-arg form, false condition: contributes nothing.
    }

    if branches.is_empty() {
        vals.push(Vec::new());
        return Ok(());
    }

    work.push(Task::Apply(Frame::IfGather {
        had_bindings,
        n: branches.len(),
    }));
    for (branch, branch_env) in branches.into_iter().rev() {
        work.push(Task::Eval {
            expr: branch,
            env: branch_env,
        });
    }
    Ok(())
}

/// Run a continuation frame: pop its child result-sets and either push a
/// finished result-set or push further work.
fn combine(
    frame: Frame,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
    budget: &AtomicI64,
) -> Result<(), String> {
    match frame {
        Frame::Gather { n } => {
            let mut out: ResultSet = Vec::new();
            for rs in pop_n(vals, n) {
                out.extend(rs);
            }
            vals.push(out);
            Ok(())
        }

        Frame::IfGather { had_bindings, n } => {
            let mut out: Vec<Atom> = Vec::new();
            for rs in pop_n(vals, n) {
                out.extend(atoms_of(&rs));
            }
            let result = match out.len() {
                0 => Vec::new(),
                1 => plain(out),
                _ if had_bindings => plain(vec![Atom::Expr(out)]),
                _ => plain(out),
            };
            vals.push(result);
            Ok(())
        }

        Frame::LetMatch { pattern, body, env } => {
            let value_rs = pop_n(vals, 1).pop().unwrap();
            let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
            for (v, _) in &value_rs {
                // Fresh match env; pattern mismatch (or match error) skips this value.
                if let Ok(Some(m)) =
                    crate::eval_parts::pattern::try_match_one(&pattern, v, &Env::new(), funcs)
                {
                    let body_env = crate::eval_parts::pattern::prepend_env(m, &env);
                    branches.push((Arc::clone(&body), body_env));
                }
            }
            if branches.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: branches.len() }));
            for (b, be) in branches.into_iter().rev() {
                work.push(Task::Eval { expr: b, env: be });
            }
            Ok(())
        }

        Frame::WithinWrap => {
            let rs = pop_n(vals, 1).pop().unwrap();
            let atoms = atoms_of(&rs);
            if atoms.is_empty() {
                return Err("within: expression produced no results".into());
            }
            let wrapped = Atom::Expr(
                std::iter::once(Atom::sym("within"))
                    .chain(atoms.into_iter())
                    .collect(),
            );
            vals.push(plain(vec![wrapped]));
            Ok(())
        }

        Frame::CollapseGather => {
            let rs = pop_n(vals, 1).pop().unwrap();
            vals.push(plain(vec![Atom::Expr(atoms_of(&rs))]));
            Ok(())
        }

        Frame::OnceCut => {
            let rs = pop_n(vals, 1).pop().unwrap();
            match rs.into_iter().next() {
                Some(pair) => vals.push(vec![pair]),
                None => vals.push(Vec::new()),
            }
            Ok(())
        }

        Frame::SuperposeUnpack => {
            let rs = pop_n(vals, 1).pop().unwrap();
            let first = rs
                .into_iter()
                .next()
                .map(|(a, _)| a)
                .ok_or_else(|| "superpose: argument produced no results".to_string())?;
            match first {
                Atom::Expr(elements) => vals.push(plain(elements)),
                other => vals.push(plain(vec![other])),
            }
            Ok(())
        }

        Frame::DataListWithHead { head, n_tail } => {
            let tail_rs = pop_n(vals, n_tail);
            let tail_atoms: Vec<Vec<Atom>> = tail_rs.iter().map(atoms_of).collect();
            // Any empty tail element collapses the whole list (non-det zero).
            if tail_atoms.iter().any(|e| e.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            let combos = cartesian_product(&tail_atoms);
            let lists: Vec<Atom> = combos
                .into_iter()
                .map(|tail_vals| {
                    let mut atoms = Vec::with_capacity(tail_vals.len() + 1);
                    atoms.push(head.clone());
                    atoms.extend(tail_vals);
                    Atom::Expr(atoms)
                })
                .collect();
            vals.push(plain(lists));
            Ok(())
        }

        Frame::DataList { n } => {
            let per_elem_rs = pop_n(vals, n);
            let per_elem: Vec<Vec<Atom>> = per_elem_rs.iter().map(atoms_of).collect();
            // Any empty element collapses the whole list (non-det zero).
            if per_elem.iter().any(|e| e.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            let combos = cartesian_product(&per_elem);
            let lists: Vec<Atom> = combos.into_iter().map(Atom::Expr).collect();
            vals.push(plain(lists));
            Ok(())
        }

        Frame::Call {
            head,
            arity,
            env,
            all_items,
        } => {
            let arg_sets = pop_n(vals, arity);
            let arg_options: Vec<Vec<Atom>> = arg_sets.iter().map(atoms_of).collect();

            match head {
                Head::Native(f) => {
                    // Empty arg result-set is a hard error for native calls.
                    if arg_options.iter().any(|v| v.is_empty()) {
                        return Err("argument produced no results".to_string());
                    }
                    let combos = cartesian_product(&arg_options);
                    let mut results: Vec<Atom> = Vec::new();
                    let mut last_err: Option<String> = None;
                    for slice in &combos {
                        match f(slice, funcs) {
                            Ok(nd) => results.extend(nd),
                            Err(e) => last_err = Some(e),
                        }
                    }
                    if results.is_empty() {
                        if let Some(e) = last_err {
                            return Err(e);
                        }
                    }
                    vals.push(plain(results));
                    Ok(())
                }

                Head::User { name, clauses } => {
                    // Empty arg result-set: fall back to data-list interpretation
                    // (mirrors try_eval_from_space returning Ok(None)).
                    if arg_options.iter().any(|v| v.is_empty()) {
                        return data_list_fallback(&all_items, &env, funcs, vals);
                    }
                    let combos = cartesian_product(&arg_options);
                    let mut bodies: Vec<(Arc<Expr>, Env, i64)> = Vec::new();
                    for combo in &combos {
                        for (patterns, body) in &clauses {
                            // Top-level `(= ...)` functions do not capture caller
                            // scope — the body sees only its own unification
                            // bindings (over an EMPTY base), not the caller's env.
                            // This is the correct lexical semantics AND prevents
                            // the binding chain from growing O(recursion depth)
                            // (which would otherwise overflow the stack when the
                            // deep Arc<Env> chain is dropped).
                            if let Some((body_env, subst_cost)) =
                                match_clause(patterns, combo, &Env::Empty, funcs)
                            {
                                bodies.push((Arc::new(body.clone()), body_env, subst_cost));
                            }
                        }
                    }
                    if bodies.is_empty() {
                        return Err(format!("no matching clause for ({})", name));
                    }
                    // Spec Query/Chain cost: c = Σ #(σᵢ) + Σ #(uᵢσᵢ) over the
                    // matched clauses. Debit the budget; halt this reduction
                    // (emit nothing) if it would be exhausted
                    // (precondition (e - c) > 0).
                    // With atomic budget: -1 = unbounded, otherwise remaining.
                    let remaining = budget.load(Ordering::Acquire);
                    if remaining >= 0 {
                        let c: i64 = bodies
                            .iter()
                            .map(|(body, body_env, subst_cost)| {
                                let instantiated_body = subst_and_atomize(body.as_ref(), body_env);
                                *subst_cost
                                    + crate::eval_parts::machine::calculate_cost(&instantiated_body)
                                        .unwrap_or(0)
                            })
                            .sum();
                        if remaining < c {
                            vals.push(Vec::new());
                            return Ok(());
                        }
                        budget.fetch_sub(c, Ordering::AcqRel);
                    }
                    work.push(Task::Apply(Frame::Gather { n: bodies.len() }));
                    for (body, body_env, _) in bodies.into_iter().rev() {
                        work.push(Task::Eval {
                            expr: body,
                            env: body_env,
                        });
                    }
                    Ok(())
                }
            }
        }
    }
}

// ========================================================================
// Helpers
// ========================================================================

/// Push a unary special form: evaluate its single argument as a CEK sub-task,
/// then run `frame` to combine. Validates arity == 1.
fn push_unary(
    args: &[Expr],
    env: &Env,
    work: &mut Vec<Task>,
    frame: Frame,
    name: &str,
) -> Result<(), String> {
    if args.len() != 1 {
        return Err(format!("{}: expected 1 arg, got {}", name, args.len()));
    }
    work.push(Task::Apply(frame));
    work.push(Task::Eval {
        expr: Arc::new(args[0].clone()),
        env: env.clone(),
    });
    Ok(())
}

/// Pop the top `n` result-sets and return them in push order (oldest first).
fn pop_n(vals: &mut Vec<ResultSet>, n: usize) -> Vec<ResultSet> {
    let at = vals.len() - n;
    vals.split_off(at)
}

/// Does `expr` contain a `$`-variable that is not bound in `env`? Such an
/// expression is a relational query needing binding propagation.
fn expr_has_unbound_var(expr: &Expr, env: &Env) -> bool {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => env.get(s).is_none(),
        Expr::List(items) => items.iter().any(|e| expr_has_unbound_var(e, env)),
        _ => false,
    }
}

/// Evaluate a sub-expression in its own isolated step loop, returning its full
/// result-set. Native stack depth grows only with static special-form nesting
/// (not runtime recursion depth), since each call runs its own iterative loop.
fn eval_sub(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<ResultSet, String> {
    // Sub-evaluations are unbudgeted; only the top reduction spine is metered.
    let mut budget = None;
    run_rs(Arc::new(expr.clone()), env.clone(), funcs, &mut budget)
}

/// Evaluate a batch of independent (pure) sub-expressions in parallel via
/// rayon, each with its own step loop sharing an atomic budget. Returns
/// result-sets in task order.
fn eval_par(
    tasks: &[(Arc<Expr>, Env)],
    funcs: &FnTable,
    budget: &Arc<AtomicI64>,
) -> Result<Vec<ResultSet>, String> {
    use rayon::prelude::*;
    tasks
        .par_iter()
        .map(|(expr, env)| {
            let mut local_work = vec![Task::Eval {
                expr: expr.clone(),
                env: env.clone(),
            }];
            let mut local_vals: Vec<ResultSet> = Vec::new();
            while let Some(task) = local_work.pop() {
                match task {
                    Task::Eval { expr, env } => {
                        dispatch(&expr, &env, funcs, &mut local_work, &mut local_vals)?
                    }
                    Task::Apply(frame) => {
                        combine(frame, funcs, &mut local_work, &mut local_vals, budget)?
                    }
                    // Nested ParEval is supported: the inner parallel tasks
                    // share the same atomic budget and run on rayon's thread
                    // pool, which handles nesting via work-stealing.
                    Task::ParEval { tasks, frame } => {
                        let rs = eval_par(&tasks, funcs, budget)?;
                        for r in rs {
                            local_vals.push(r);
                        }
                        local_work.push(Task::Apply(*frame));
                    }
                }
            }
            Ok(local_vals.pop().unwrap_or_default())
        })
        .collect()
}

/// Push a data-list evaluation: evaluate every item, then combine via cartesian.
fn dispatch_data_list(items: &[Expr], env: &Env, work: &mut Vec<Task>) {
    work.push(Task::Apply(Frame::DataList { n: items.len() }));
    for item in items.iter().rev() {
        work.push(Task::Eval {
            expr: Arc::new(item.clone()),
            env: env.clone(),
        });
    }
}

/// Dispatch a call whose head has resolved to a concrete atom (from a `$var` or
/// a compound operator): a symbol re-enters call dispatch, a closure is applied,
/// anything else becomes a data list with that head.
fn dispatch_resolved_head(
    head: Atom,
    args: &[Expr],
    all_items: &[Expr],
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    match &head {
        Atom::Sym(name) => {
            let arity = args.len() as u8;
            // Only dispatch as a function call if the symbol is actually a known
            // function at this arity. Otherwise the whole list is data, and the
            // head has already been evaluated (extracted from the compound-head
            // path). Pushing DataListWithHead prevents double-evaluating the
            // head expression — which would break side-effectful expressions
            // like (add-atom ...).
            if funcs.get(name, arity).is_some() || lookup_user_clauses(name, arity, funcs).is_some()
            {
                dispatch_call(name, args, all_items, env, funcs, work)
            } else {
                work.push(Task::Apply(Frame::DataListWithHead {
                    head: head.clone(),
                    n_tail: args.len(),
                }));
                for arg in args.iter().rev() {
                    work.push(Task::Eval {
                        expr: Arc::new(arg.clone()),
                        env: env.clone(),
                    });
                }
                Ok(())
            }
        }
        Atom::Closure(c) => {
            let rs = cek_apply_closure(&c.params, &c.body, &c.env, args, env, funcs)?;
            vals.push(rs);
            Ok(())
        }
        other => {
            // Data list with a pre-evaluated head atom.
            let mut per: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
            for a in args {
                per.push(atoms_of(&eval_sub(a, env, funcs)?));
            }
            if per.iter().any(|v| v.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            let lists: Vec<Atom> = cartesian_product(&per)
                .into_iter()
                .map(|combo| {
                    let mut v = Vec::with_capacity(combo.len() + 1);
                    v.push(other.clone());
                    v.extend(combo);
                    Atom::Expr(v)
                })
                .collect();
            vals.push(plain(lists));
            Ok(())
        }
    }
}

/// Apply a closure (mirrors `core::apply_closure`) using isolated sub-evaluation.
fn cek_apply_closure(
    params: &[Expr],
    body: &Expr,
    capture_env: &Env,
    args: &[Expr],
    call_env: &Env,
    funcs: &FnTable,
) -> Result<ResultSet, String> {
    if params.len() != args.len() {
        return Err(format!(
            "closure: expected {} arguments, got {}",
            params.len(),
            args.len()
        ));
    }
    let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
    for arg in args {
        let vals = atoms_of(&eval_sub(arg, call_env, funcs)?);
        if vals.is_empty() {
            return Err("closure: argument produced no results".into());
        }
        arg_options.push(vals);
    }
    let combos = cartesian_product(&arg_options);
    let single_combo = combos.len() == 1;
    let mut out: ResultSet = Vec::new();
    for combo in &combos {
        let mut menv = Env::new();
        let mut mismatch: Option<String> = None;
        for (pat, val) in params.iter().zip(combo.iter()) {
            match crate::eval_parts::pattern::try_match_one(pat, val, &menv, funcs)? {
                Some(e) => menv = e,
                None => {
                    mismatch = Some(format!(
                        "closure: pattern {} does not match argument {}",
                        pat.to_string(),
                        val.to_sexpr_string()
                    ));
                    break;
                }
            }
        }
        if let Some(msg) = mismatch {
            if single_combo {
                return Err(msg);
            }
            continue;
        }
        let fenv = crate::eval_parts::pattern::prepend_env(menv, capture_env);
        out.extend(eval_sub(body, &fenv, funcs)?);
    }
    Ok(out)
}

/// `let*`: evaluate bindings sequentially (first result each), returning the
/// environment in which the body should be evaluated.
fn cek_let_star_env(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<Env, String> {
    if args.len() != 2 {
        return Err(format!(
            "let*: expected ((bindings) body), got {} args",
            args.len()
        ));
    }
    let bindings = match &args[0] {
        Expr::List(items) => items,
        _ => return Err("let*: first arg must be a list of (pattern val) pairs".into()),
    };
    let mut cur = env.clone();
    for pair in bindings {
        match pair {
            Expr::List(p) if p.len() == 2 => {
                let pattern = &p[0];
                let val = eval_sub(&p[1], &cur, funcs)?
                    .into_iter()
                    .next()
                    .map(|(a, _)| a)
                    .ok_or_else(|| {
                        format!("let*: binding {} produced no value", pattern.to_string())
                    })?;
                let m =
                    crate::eval_parts::pattern::try_match_one(pattern, &val, &Env::new(), funcs)?
                        .ok_or_else(|| {
                        format!(
                            "let*: pattern does not match value: {} vs {}",
                            pattern.to_string(),
                            val.to_sexpr_string()
                        )
                    })?;
                cur = crate::eval_parts::pattern::prepend_env(m, &cur);
            }
            _ => return Err("let*: each binding must be a (pattern val) pair".into()),
        }
    }
    Ok(cur)
}

/// `chain`: thread `(expr $var)` pairs (first result each), returning the final
/// expression and the environment to evaluate it in.
fn cek_chain_env(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<(Arc<Expr>, Env), String> {
    if args.len() < 3 || args.len() % 2 == 0 {
        return Err(format!(
            "chain: expected odd number of args (expr $var expr ...), got {}",
            args.len()
        ));
    }
    let mut cur = env.clone();
    let pairs = args.len() / 2;
    for i in 0..pairs {
        let expr = &args[i * 2];
        let var = &args[i * 2 + 1];
        let var_name = match var {
            Expr::Symbol(s) if s.starts_with('$') => s.clone(),
            _ => {
                return Err(format!(
                    "chain: arg {} must be a $variable, got {}",
                    i * 2 + 1,
                    var.to_string()
                ));
            }
        };
        let val = eval_sub(expr, &cur, funcs)?
            .into_iter()
            .next()
            .map(|(a, _)| a)
            .ok_or_else(|| format!("chain: expression {} produced no results", i * 2))?;
        cur = cur.extend(&var_name, val);
    }
    Ok((Arc::new(args[args.len() - 1].clone()), cur))
}

/// `progn`: replicate the let-leak AST rewrite, pushing the last form (or the
/// rewritten expression) as a task so its recursion stays iterative.
fn cek_progn(
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
) -> Result<(), String> {
    if args.is_empty() {
        return Err("progn: expected at least one form".into());
    }
    let sym = |s: &str| Expr::Symbol(s.to_string());
    let len = args.len();
    for i in 0..len {
        let arg = &args[i];
        if i + 1 < len {
            if let Expr::List(items) = arg {
                if items.len() == 4 && items[0] == sym("let") {
                    let mut rest = vec![items[3].clone()];
                    rest.extend_from_slice(&args[i + 1..]);
                    let new_progn = Expr::List(std::iter::once(sym("progn")).chain(rest).collect());
                    let new_let = Expr::List(vec![
                        sym("let"),
                        items[1].clone(),
                        items[2].clone(),
                        new_progn,
                    ]);
                    work.push(Task::Eval {
                        expr: Arc::new(new_let),
                        env: env.clone(),
                    });
                    return Ok(());
                } else if items.len() == 3 && items[0] == sym("let*") {
                    let mut rest = vec![items[2].clone()];
                    rest.extend_from_slice(&args[i + 1..]);
                    let new_progn = Expr::List(std::iter::once(sym("progn")).chain(rest).collect());
                    let new_let = Expr::List(vec![sym("let*"), items[1].clone(), new_progn]);
                    work.push(Task::Eval {
                        expr: Arc::new(new_let),
                        env: env.clone(),
                    });
                    return Ok(());
                } else if items.len() == 4 && items[0] == sym("match") {
                    if let Expr::Symbol(s) = &items[3] {
                        if s.starts_with('$') {
                            let rest: Vec<Expr> = args[i + 1..].to_vec();
                            let new_progn =
                                Expr::List(std::iter::once(sym("progn")).chain(rest).collect());
                            let new_let = Expr::List(vec![
                                sym("let"),
                                items[3].clone(),
                                arg.clone(),
                                new_progn,
                            ]);
                            work.push(Task::Eval {
                                expr: Arc::new(new_let),
                                env: env.clone(),
                            });
                            return Ok(());
                        }
                    }
                }
            }
        }
        if i == len - 1 {
            work.push(Task::Eval {
                expr: Arc::new(arg.clone()),
                env: env.clone(),
            });
            return Ok(());
        }
        // Intermediate form: evaluate for effect, discard.
        eval_sub(arg, env, funcs)?;
    }
    Err("progn: internal — no forms after empty check".into())
}

/// `case`: evaluate the scrutinee, then push the matching clause body per value
/// as a task (bodies stay iterative).
fn cek_case(
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    if args.len() != 2 {
        return Err(format!(
            "case: expected (expr (clauses...)), got {} args",
            args.len()
        ));
    }
    let clauses = match &args[1] {
        Expr::List(items) => items,
        _ => return Err("case: second arg must be a list of (pattern body) pairs".into()),
    };

    let srs = eval_sub(&args[0], env, funcs)?;
    if srs.is_empty() {
        // Empty scrutinee: look for an (Empty body) clause.
        for clause in clauses {
            if let Expr::List(items) = clause {
                if items.len() == 2 && matches!(&items[0], Expr::Symbol(s) if s == "Empty") {
                    work.push(Task::Eval {
                        expr: Arc::new(items[1].clone()),
                        env: env.clone(),
                    });
                    return Ok(());
                }
            }
        }
        vals.push(Vec::new());
        return Ok(());
    }

    let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
    for (v, _) in &srs {
        let (body, benv) = match_case_clause(v, clauses, env, funcs)?;
        branches.push((Arc::new(body), benv));
    }
    work.push(Task::Apply(Frame::Gather { n: branches.len() }));
    for (b, be) in branches.into_iter().rev() {
        work.push(Task::Eval { expr: b, env: be });
    }
    Ok(())
}

/// Find the first matching `case` clause for `val`, returning its body and the
/// environment to evaluate it in. `$else` is a catch-all; `Empty` is skipped.
fn match_case_clause(
    val: &Atom,
    clauses: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<(Expr, Env), String> {
    for clause in clauses {
        let (pattern, body) = match clause {
            Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
            _ => {
                return Err(format!(
                    "case: each clause must be (pattern body), got {}",
                    clause.to_string()
                ));
            }
        };
        if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
            continue;
        }
        if matches!(pattern, Expr::Symbol(s) if s == "$else") {
            return Ok((body.clone(), env.clone()));
        }
        if let Some(m) =
            crate::eval_parts::pattern::try_match_one(pattern, val, &Env::new(), funcs)?
        {
            return Ok((
                body.clone(),
                crate::eval_parts::pattern::prepend_env(m, env),
            ));
        }
    }
    Err(format!(
        "case: no clause matched value {}",
        val.to_sexpr_string()
    ))
}

/// `foldall` (mirrors `eval_foldall`) via isolated sub-evaluation.
fn cek_foldall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<ResultSet, String> {
    if args.len() != 3 {
        return Err(format!(
            "foldall: expected (agg-func gen-expr init), got {} args",
            args.len()
        ));
    }
    let agg_func = &args[0];
    let gen_values: Vec<Atom> = match eval_sub(&args[1], env, funcs) {
        Ok(rs) => atoms_of(&rs),
        Err(_) => generate_free_var_values(&args[1], env, funcs)?,
    };
    let init = eval_sub(&args[2], env, funcs)?
        .into_iter()
        .next()
        .map(|(a, _)| a)
        .ok_or_else(|| "foldall: init expression produced no results".to_string())?;
    let accum = gen_values.into_iter().try_fold(init, |acc, val| {
        let acc_expr = atom_to_expr(&acc)?;
        let val_expr = atom_to_expr(&val)?;
        let call = Expr::List(vec![agg_func.clone(), acc_expr, val_expr]);
        eval_sub(&call, env, funcs)?
            .into_iter()
            .next()
            .map(|(a, _)| a)
            .ok_or_else(|| "foldall: aggregate function produced no results".to_string())
    })?;
    Ok(plain(vec![accum]))
}

/// `map-atom` (mirrors `eval_map_atom`) via isolated sub-evaluation.
fn cek_map_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<ResultSet, String> {
    if args.len() != 2 {
        return Err(format!(
            "map-atom: expected (list func), got {} args",
            args.len()
        ));
    }
    let list_atom = eval_sub(&args[0], env, funcs)?
        .into_iter()
        .next()
        .map(|(a, _)| a)
        .ok_or_else(|| "map-atom: list expression produced no results".to_string())?;
    let func_atom = eval_sub(&args[1], env, funcs)?
        .into_iter()
        .next()
        .map(|(a, _)| a)
        .ok_or_else(|| "map-atom: func expression produced no results".to_string())?;
    let elements = match list_atom {
        Atom::Expr(items) => items,
        other => {
            return Err(format!(
                "map-atom: expected a list (Expr), got {}",
                other.to_sexpr_string()
            ));
        }
    };
    let mut results = Vec::with_capacity(elements.len());
    for elem in &elements {
        let result = match &func_atom {
            Atom::Sym(fname) => {
                let call = Expr::List(vec![Expr::Symbol(fname.to_string()), atom_to_expr(elem)?]);
                eval_sub(&call, env, funcs)?
                    .into_iter()
                    .next()
                    .map(|(a, _)| a)
                    .ok_or_else(|| {
                        format!(
                            "map-atom: {} returned no result for {}",
                            fname,
                            elem.to_sexpr_string()
                        )
                    })?
            }
            Atom::Closure(c) => cek_apply_closure(
                &c.params,
                &c.body,
                &c.env,
                &[atom_to_expr(elem)?],
                env,
                funcs,
            )?
            .into_iter()
            .next()
            .map(|(a, _)| a)
            .ok_or_else(|| {
                format!(
                    "map-atom: closure returned no result for {}",
                    elem.to_sexpr_string()
                )
            })?,
            _ => Atom::Expr(vec![func_atom.clone(), elem.clone()]),
        };
        results.push(result);
    }
    Ok(plain(vec![Atom::Expr(results)]))
}

/// `forall` (mirrors `eval_forall`) via isolated sub-evaluation.
fn cek_forall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<ResultSet, String> {
    if args.len() != 2 {
        return Err(format!("forall: expected 2 args, got {}", args.len()));
    }
    let gen_values: Vec<Atom> = eval_constrained(&args[0], env, funcs)?
        .into_iter()
        .map(|(a, _)| a)
        .collect();
    let check = eval_sub(&args[1], env, funcs)?
        .into_iter()
        .next()
        .map(|(a, _)| a)
        .ok_or_else(|| "forall: check produced no value".to_string())?;

    let arg_sym = Expr::Symbol("$__fv".to_string());
    for val in gen_values {
        let call_env = env.extend("$__fv", val);
        let results: Vec<Atom> = match &check {
            Atom::Sym(fname) => {
                let call = Expr::List(vec![Expr::Symbol(fname.to_string()), arg_sym.clone()]);
                atoms_of(&eval_sub(&call, &call_env, funcs)?)
            }
            Atom::Closure(c) => atoms_of(&cek_apply_closure(
                &c.params,
                &c.body,
                &c.env,
                &[arg_sym.clone()],
                &call_env,
                funcs,
            )?),
            other => {
                return Err(format!(
                    "forall: check must be a function or closure, got {}",
                    other.to_sexpr_string()
                ));
            }
        };
        if results.is_empty() || !results.iter().all(|a| a.is_truthy()) {
            return Ok(plain(vec![Atom::sym("false")]));
        }
    }
    Ok(plain(vec![Atom::sym("true")]))
}

/// Is `s` a special-form keyword (operator not evaluated)?
pub(crate) fn is_special_form(s: &str) -> bool {
    matches!(
        s,
        "if" | "progn"
            | "let"
            | "let*"
            | "quote"
            | "call"
            | "reduce"
            | "eval"
            | "transform"
            | "add-atom"
            | "remove-atom"
            | "match"
            | "import!"
            | "readln!"
            | "println!"
            | "superpose"
            | "collapse"
            | "chain"
            | "case"
            | "foldall"
            | "map-atom"
            | "|->"
            | "forall"
            | "repr"
            | "within"
            | "empty"
            | "once"
            | "py-call"
            | "import-rs!"
    )
}

/// Sum the costs of all bindings in a unification environment.
fn env_binding_cost(env: &Env) -> i64 {
    let mut total = 0;
    let mut current = env;
    loop {
        match current {
            Env::Empty => return total,
            Env::Cons { value, next, .. } => {
                total += crate::eval_parts::machine::calculate_cost(value).unwrap_or(0);
                current = next.as_ref();
            }
        }
    }
}

fn match_clause(
    patterns: &[Expr],
    args: &[Atom],
    env: &Env,
    funcs: &FnTable,
) -> Option<(Env, i64)> {
    let mut unif = Env::new();
    for (pat, arg) in patterns.iter().zip(args.iter()) {
        match crate::eval_parts::pattern::try_match_one(pat, arg, &unif, funcs) {
            Ok(Some(new_env)) => unif = new_env,
            _ => return None,
        }
    }
    let subst_cost = env_binding_cost(&unif);
    Some((
        crate::eval_parts::pattern::prepend_env(unif, env),
        subst_cost,
    ))
}

/// Look up the `(patterns, body)` clauses for `name/arity`: from the function
/// cache first, falling back to a direct space query. Returns `None` when no
/// definition exists at all (caller then treats the list as data).
fn lookup_user_clauses(name: &str, arity: u8, funcs: &FnTable) -> Option<Vec<(Vec<Expr>, Expr)>> {
    if let Some(inner) = funcs.fn_cache.read().unwrap().get(name) {
        if let Some(clauses) = inner.get(&arity) {
            return Some(
                clauses
                    .iter()
                    .map(|c| (c.patterns.clone(), c.body.clone()))
                    .collect(),
            );
        }
    }

    // Cache miss: query the space for `(= (name _ ...) _)` definitions.
    eprintln!("CACHE MISS: name={}, arity={}", name, arity);
    let mut head_patterns: Vec<crate::space::Pattern> =
        vec![crate::space::Pattern::Exact(Atom::sym(name))];
    for _ in 0..arity {
        head_patterns.push(crate::space::Pattern::Any);
    }
    let def_pattern = crate::space::Pattern::Expr(vec![
        crate::space::Pattern::Exact(Atom::sym("=")),
        crate::space::Pattern::Expr(head_patterns),
        crate::space::Pattern::Any,
    ]);
    let matches = funcs.space.read().unwrap().match_atoms(&def_pattern);
    if matches.is_empty() {
        return None;
    }

    let mut clauses: Vec<(Vec<Expr>, Expr)> = Vec::new();
    for m in &matches {
        if let Atom::Expr(parts) = &m.atom {
            if parts.len() == 3 {
                if let Atom::Expr(head_items) = &parts[1] {
                    if head_items.len() == arity as usize + 1 {
                        let patterns: Vec<Expr> = head_items[1..]
                            .iter()
                            .map(|a| {
                                atom_to_expr(a)
                                    .unwrap_or_else(|_| Expr::Symbol(a.to_sexpr_string()))
                            })
                            .collect();
                        let body = atom_to_expr(&parts[2])
                            .unwrap_or_else(|_| Expr::Symbol(parts[2].to_sexpr_string()));
                        clauses.push((patterns, body));
                    }
                }
            }
        }
    }
    if clauses.is_empty() {
        None
    } else {
        Some(clauses)
    }
}

/// Evaluate `all_items` as a data list via the recursive evaluator and push the
/// result-set. Used only for the rare empty-arg fallback.
fn data_list_fallback(
    all_items: &[Expr],
    env: &Env,
    funcs: &FnTable,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    let list = Expr::List(all_items.to_vec());
    let nd = crate::eval_parts::core::eval(&list, env, funcs)?;
    vals.push(plain(nd.collect()));
    Ok(())
}
