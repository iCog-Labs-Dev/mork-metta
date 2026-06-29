//! Helpers for closures and delayed arguments.
//!
//! This module contains support code for closure application and delayed
//! argument handling used during evaluation.
use crate::parser::Expr;

/// Return `true` when every occurrence of a variable appears only under
/// an `(eval var)` form in a function body.
fn is_eval_only_param(body: &Expr, var: &str) -> bool {
    fn walk(expr: &Expr, var: &str, seen: &mut bool, ok: &mut bool) {
        match expr {
            Expr::List(items)
                if items.len() == 2
                    && matches!(&items[0], Expr::Symbol(symbol) if symbol == "eval")
                    && matches!(&items[1], Expr::Symbol(symbol) if symbol == var) =>
            {
                *seen = true;
            }
            Expr::List(items) => {
                for item in items.iter() {
                    walk(item, var, seen, ok);
                    if !*ok {
                        return;
                    }
                }
            }
            Expr::Symbol(symbol) if symbol == var => {
                *seen = true;
                *ok = false;
            }
            _ => {}
        }
    }

    let mut seen = false;
    let mut ok = true;
    walk(body, var, &mut seen, &mut ok);
    seen && ok
}

/// Compute the lazy argument mask for a set of user-function clauses.
///
/// A slot is lazy when every clause uses the corresponding variable only as an
/// explicit argument to `eval` — or when the entire body is directly `(== var ...)`
/// or `(!= var ...)` with the variable as a direct (non-nested) argument,
/// indicating the function preserves expression structure for structural comparison.
pub(crate) fn lazy_user_arg_mask(clauses: &[(&[Expr], &Expr)]) -> Vec<bool> {
    let Some((patterns, _)) = clauses.first() else {
        return Vec::new();
    };

    let arity = patterns.len();
    (0..arity)
        .map(|index| {
            clauses.iter().all(|(patterns, body)| {
                patterns.len() == arity
                    && matches!(
                        &patterns[index],
                        Expr::Symbol(name) if name.starts_with('$')
                            && (is_eval_only_param(body, name) || is_eq_direct_body(body, name))
                    )
            })
        })
        .collect()
}

/// Return `true` when the body is directly `(== $var ...)` or `(!= $var ...)`
/// with `var` as a direct (non-nested) argument — the variable is used as a
/// raw expression for structural comparison.
fn is_eq_direct_body(body: &Expr, var: &str) -> bool {
    matches!(body,
        Expr::List(items) if items.len() >= 2
            && matches!(&items[0], Expr::Symbol(s)
                if s == "==" || s == "!=")
            && items[1..].iter().any(|item|
                matches!(item, Expr::Symbol(s) if s == var))
            && !items[1..].iter().any(|item|
                matches!(item, Expr::List(_))
                    && contains_var(item, var))
    )
}

/// Return `true` when `var` appears anywhere in the expression tree.
fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Symbol(s) => s == var,
        Expr::List(items) => items.iter().any(|item| contains_var(item, var)),
        _ => false,
    }
}
