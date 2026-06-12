/// Data list evaluation: when a list's first element is not a known function
/// or special form, the entire list is treated as data.
///
/// # Semantics
///
/// Each element is evaluated and the results are collected into a single
/// `Atom::Expr`. This matches PeTTa semantics where `(1 2 3)` produces one
/// list value `[1, 2, 3]`, not three separate results.
///
/// Pure lists (all elements are pure expressions) can be evaluated in
/// parallel via Rayon. Impure lists fall back to sequential evaluation to
/// preserve side-effect ordering.

use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::core::eval;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

/// Evaluate a list as data: each element is evaluated and collected into a
/// single `Atom::Expr`.
///
/// (including nested function calls), then collected into one list atom.
pub(crate) fn eval_data_list(items: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    eval_data_list_par(items, env, funcs)
}

/// Like `eval_data_list`, but the head element was already evaluated by the
/// caller (operator-position dispatch in `try_call_or_data`). Reusing that
/// value instead of re-evaluating prevents side-effecting heads
/// (e.g. add-atom, println!) from running twice.
pub(crate) fn eval_data_list_with_head(
    head: Atom,
    rest: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    let all_pure = worth_parallel(rest) && rest.iter().all(|item| is_pure_expr(item, funcs));
    if all_pure {
        use rayon::prelude::*;
        let mut atoms = Vec::with_capacity(rest.len() + 1);
        atoms.push(head);
        let results: Vec<Result<Option<Atom>, String>> = rest.par_iter()
            .map(|item| eval_data_item(item, env, funcs))
            .collect();
        for r in results {
            match r? {
                Some(a) => atoms.push(a),
                None => return Ok(NDet::stream(std::iter::empty())),
            }
        }
        Ok(NDet::single(Atom::Expr(atoms)))
    } else {
        let mut atoms = Vec::with_capacity(rest.len() + 1);
        atoms.push(head);
        for item in rest {
            match eval_data_item(item, env, funcs)? {
                Some(a) => atoms.push(a),
                None => return Ok(NDet::stream(std::iter::empty())),
            }
        }
        Ok(NDet::single(Atom::Expr(atoms)))
    }
}

/// Count of currently-active parallel fork regions. Used as a saturation
/// gate: once enough concurrent forks exist to feed every worker, deeper
/// recursion levels evaluate sequentially. Without this, recursive functions
/// fork at EVERY level — exponentially many micro-tasks whose scheduling
/// overhead dwarfs the work (observed: 10x CPU burn for 4x wall-clock).
static ACTIVE_FORKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// RAII guard for a parallel fork region.
pub(crate) struct ForkGuard;
impl Drop for ForkGuard {
    fn drop(&mut self) {
        ACTIVE_FORKS.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// Try to claim a fork slot. Returns a guard while the pool is unsaturated,
/// `None` once active forks ≥ worker count (callers then go sequential).
pub(crate) fn try_fork() -> Option<ForkGuard> {
    let limit = rayon::current_num_threads();
    let prev = ACTIVE_FORKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if prev < limit {
        Some(ForkGuard)
    } else {
        ACTIVE_FORKS.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
        None
    }
}

/// Heuristic: is parallel evaluation of these expressions worth the rayon
/// task overhead? Only when at least two of them are compound (non-empty
/// lists). Symbols and numbers evaluate in nanoseconds — forking for them
/// creates a micro-task storm that costs far more than it saves.
pub(crate) fn worth_parallel(items: &[Expr]) -> bool {
    items.iter()
        .filter(|e| matches!(e, Expr::List(l) if !l.is_empty()))
        .count() >= 2
}

/// Recursively check if an expression is pure (no side effects).
/// Pure expressions can be evaluated in parallel.
pub(crate) fn is_pure_expr(expr: &Expr, funcs: &FnTable) -> bool {
    is_pure_expr_inner(expr, funcs, None)
}

/// Purity check used at definition time: occurrences of `self_name` in call
/// position are optimistically assumed pure, so directly-recursive functions
/// (e.g. fib) can be inferred pure from an otherwise-pure body.
pub(crate) fn is_pure_expr_assuming(expr: &Expr, funcs: &FnTable, self_name: &str) -> bool {
    is_pure_expr_inner(expr, funcs, Some(self_name))
}

fn is_pure_expr_inner(expr: &Expr, funcs: &FnTable, assume_pure: Option<&str>) -> bool {
    match expr {
        Expr::Number(_) => true,
        // $var lookups are pure (read-only env access);
        // plain symbols are pure (self-evaluating)
        Expr::Symbol(_) => true,
        Expr::List(items) if items.is_empty() => true,
        Expr::List(items) => {
            let op = &items[0];
            let args_pure =
                || items[1..].iter().all(|e| is_pure_expr_inner(e, funcs, assume_pure));
            if let Expr::Symbol(s) = op {
                match s.as_str() {
                    // Pure regardless of args (args not evaluated / no effects)
                    "quote" | "superpose" | "empty" | "repr" | "|->" => true,
                    // Control forms: pure iff every subexpression is pure
                    "if" | "progn" | "let" | "let*" | "chain" | "collapse" => args_pure(),
                    // Effectful or opaque special forms
                    "eval" | "call" | "reduce"
                    | "add-atom" | "remove-atom" | "match" | "import!" | "readln!"
                    | "println!" | "case" | "foldall" | "map-atom"
                    | "forall" | "within" | "py-call" | "import-rs!" => false,
                    // Function call: callee must be pure (or the function being
                    // defined, assumed pure) AND every argument must be pure —
                    // a pure callee does not launder impure args.
                    _ => {
                        let callee_pure = assume_pure == Some(s.as_str())
                            || funcs.is_pure(s, (items.len() - 1) as u8);
                        callee_pure && args_pure()
                    }
                }
            } else {
                // Dynamic operator (expression that evaluates to a function name)
                false
            }
        }
    }
}

/// Evaluate a data list in parallel when all elements are pure.
/// Otherwise, evaluates sequentially (preserves side-effect ordering).
pub(crate) fn eval_data_list_par(items: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let all_pure = worth_parallel(items) && items.iter().all(|item| is_pure_expr(item, funcs));
    if all_pure {
        use rayon::prelude::*;
        let results: Vec<Result<Option<Atom>, String>> = items.par_iter()
            .map(|item| eval_data_item(item, env, funcs))
            .collect();
        let mut atoms = Vec::with_capacity(items.len());
        for r in results {
            match r? {
                Some(a) => atoms.push(a),
                None => return Ok(NDet::stream(std::iter::empty())),
            }
        }
        Ok(NDet::single(Atom::Expr(atoms)))
    } else {
        // Sequential path (preserves order + side-effect visibility)
        let mut atoms = Vec::with_capacity(items.len());
        for item in items {
            match eval_data_item(item, env, funcs)? {
                Some(a) => atoms.push(a),
                None => return Ok(NDet::stream(std::iter::empty())),
            }
        }
        Ok(NDet::single(Atom::Expr(atoms)))
    }
}

/// Evaluate one element of a data list. Returns `None` if the expression produces
/// no results (empty NDet), which callers propagate as empty.
pub(crate) fn eval_data_item(item: &Expr, env: &Env, funcs: &FnTable) -> Result<Option<Atom>, String> {
    match item {
        Expr::Number(n) => Ok(Some(Atom::Num(*n))),
        Expr::Symbol(s) => {
            if s.starts_with('$') {
                Ok(Some(env.get(s).unwrap_or_else(|| Atom::sym(s))))
            } else {
                Ok(Some(Atom::sym(s)))
            }
        }
        Expr::List(inner) => {
            if inner.is_empty() {
                Ok(Some(Atom::Expr(vec![])))
            } else {
                Ok(eval(item, env, funcs)?.next())
            }
        }
    }
}
