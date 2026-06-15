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
use crate::eval_parts::constrained::cartesian_product;

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
    let per_elem = eval_elements(rest, env, funcs)?;
    if per_elem.iter().any(|e| e.is_empty()) {
        return Ok(NDet::stream(std::iter::empty()));
    }
    // Cartesian-product the tail; prepend the (already-evaluated) head to each.
    let combos = cartesian_product(&per_elem);
    let lists: Vec<Atom> = combos
        .into_iter()
        .map(|rest_vals| {
            let mut atoms = Vec::with_capacity(rest_vals.len() + 1);
            atoms.push(head.clone());
            atoms.extend(rest_vals);
            Atom::Expr(atoms)
        })
        .collect();
    Ok(NDet::stream(lists.into_iter()))
}

// Nested parallelism is bounded by rayon's work-stealing scheduler itself: when
// the pool is saturated, `par_iter`/`join` run inline on the current worker
// instead of spawning, so recursion does NOT create exponential live tasks. No
// global fork counter is needed (it only added cross-thread atomic contention
// and made the parallel/sequential choice depend on wall-clock timing, i.e.
// non-reproducible). Granularity is gated cheaply by `worth_parallel` below.

/// Heuristic: is parallel evaluation of these expressions worth the rayon
/// task overhead? Only when at least two of them are compound (non-empty
/// lists). Symbols and numbers evaluate in nanoseconds — forking for them
/// creates a micro-task storm that costs far more than it saves.
pub(crate) fn worth_parallel(items: &[Expr]) -> bool {
    items
        .iter()
        .filter(|e| matches!(e, Expr::List(l) if !l.is_empty()))
        .count()
        >= 2
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
            let args_pure = || {
                items[1..]
                    .iter()
                    .all(|e| is_pure_expr_inner(e, funcs, assume_pure))
            };
            if let Expr::Symbol(s) = op {
                match s.as_str() {
                    // Pure regardless of args (args not evaluated / no effects)
                    "quote" | "superpose" | "empty" | "repr" | "|->" | "once" => true,
                    // Control forms: pure iff every subexpression is pure
                    "if" | "progn" | "let" | "let*" | "chain" | "collapse" => args_pure(),
                    // Effectful or opaque special forms
                    "eval" | "call" | "reduce" | "assert" | "transform" | "add-atom"
                    | "remove-atom" | "match" | "with_mutex" | "transaction" | "import!"
                    | "readln!" | "println!" | "case" | "foldall" | "map-atom" | "forall"
                    | "within" | "py-call" | "import-rs!" => false,
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

/// Evaluate every element of a list to its FULL result set (parallel when all
/// elements are pure, else sequential to preserve side-effect ordering).
/// Returns one `Vec<Atom>` per element — the element's complete non-deterministic
/// result multiset, which the caller cartesian-products into list values.
fn eval_elements(items: &[Expr], env: &Env, funcs: &FnTable) -> Result<Vec<Vec<Atom>>, String> {
    let all_pure = worth_parallel(items) && items.iter().all(|item| is_pure_expr(item, funcs));
    if all_pure {
        use rayon::prelude::*;
        let results: Vec<Result<Vec<Atom>, String>> = items
            .par_iter()
            .map(|item| eval_data_item_all(item, env, funcs))
            .collect();
        let mut per_elem = Vec::with_capacity(items.len());
        for r in results {
            per_elem.push(r?);
        }
        Ok(per_elem)
    } else {
        let mut per_elem = Vec::with_capacity(items.len());
        for item in items {
            per_elem.push(eval_data_item_all(item, env, funcs)?);
        }
        Ok(per_elem)
    }
}

/// Evaluate a data list, preserving non-determinism. Each element contributes
/// its full result set; the list value is the cartesian product of those sets
/// (so `(a (superpose (1 2)))` yields both `(a 1)` and `(a 2)`). When every
/// element is deterministic this is exactly one list — identical to before.
pub(crate) fn eval_data_list_par(
    items: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    let per_elem = eval_elements(items, env, funcs)?;
    // Any element with no results collapses the whole list to empty (non-det zero).
    if per_elem.iter().any(|e| e.is_empty()) {
        return Ok(NDet::stream(std::iter::empty()));
    }
    let combos = cartesian_product(&per_elem);
    let lists: Vec<Atom> = combos.into_iter().map(Atom::Expr).collect();
    Ok(NDet::stream(lists.into_iter()))
}

/// Evaluate one element of a data list to its complete result multiset.
/// An empty vec means the element produced no results (caller propagates empty).
pub(crate) fn eval_data_item_all(
    item: &Expr,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<Atom>, String> {
    match item {
        Expr::Number(n) => Ok(vec![Atom::Num(*n)]),
        Expr::Symbol(s) => {
            if s.starts_with('$') {
                Ok(vec![env.get(s).unwrap_or_else(|| Atom::sym(s))])
            } else {
                Ok(vec![Atom::sym(s)])
            }
        }
        Expr::List(inner) => {
            if inner.is_empty() {
                Ok(vec![Atom::Expr(vec![])])
            } else {
                Ok(eval(item, env, funcs)?.collect())
            }
        }
    }
}
