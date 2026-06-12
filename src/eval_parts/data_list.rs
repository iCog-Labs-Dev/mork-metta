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
    let all_pure = rest.iter().all(|item| is_pure_expr(item, funcs));
    if all_pure && rest.len() > 1 {
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

/// Recursively check if an expression is pure (no side effects).
/// Pure expressions can be evaluated in parallel.
pub(crate) fn is_pure_expr(expr: &Expr, funcs: &FnTable) -> bool {
    match expr {
        Expr::Number(_) => true,
        Expr::Symbol(s) => {
            // $var lookups are pure (read-only env access)
            // Plain symbols are pure (self-evaluating)
            true
        }
        Expr::List(items) if items.is_empty() => true,
        Expr::List(items) => {
            let op = &items[0];
            if let Expr::Symbol(s) = op {
                match s.as_str() {
                    // Pure special forms
                    "quote" | "collapse" | "superpose" | "empty" | "repr" => true,
                    // Impure special forms
                    "if" | "progn" | "let" | "let*" | "eval" | "call" | "reduce"
                    | "add-atom" | "remove-atom" | "match" | "import!" | "readln!"
                    | "println!" | "chain" | "case" | "foldall" | "map-atom"
                    | "|->" | "forall" | "within" | "py-call" | "import-rs!" => false,
                    // User-defined or native function — check table
                    _ => funcs.is_pure(s, (items.len() - 1) as u8),
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
    let all_pure = items.iter().all(|item| is_pure_expr(item, funcs));
    if all_pure && items.len() > 1 {
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
