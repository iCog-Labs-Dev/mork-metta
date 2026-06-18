//! Helpers for closures and delayed arguments.
//!
//! This module contains support code for closure application and delayed
//! argument handling used during evaluation.

use crate::atom::{Atom, ClosureData};
use crate::env::Env;
use crate::func::FnTable;
use crate::parser::Expr;

use super::subst::subst_and_atomize;

/// Return an unreduced atom for argument shapes that must be preserved during
/// user-function application.
pub(crate) fn definition_arg_atom(expr: &Expr, env: &Env) -> Option<Atom> {
    match expr {
        Expr::List(items) if !items.is_empty() => match &items[0] {
            Expr::Symbol(symbol) if symbol == "=" && items.len() == 3 => {
                Some(subst_and_atomize(expr, env))
            }
            // Preserve (quote ...) as data — eager evaluation would strip the
            // quote wrapper, breaking pattern matching in user functions like
            //   (= (unquote (quote $A)) ...)
            Expr::Symbol(symbol) if symbol == "quote" && items.len() == 2 => {
                Some(subst_and_atomize(expr, env))
            }
            _ => None,
        },
        _ => None,
    }
}

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

/// Wrap an unevaluated user-function argument as a zero-argument closure.
pub(crate) fn delayed_user_call_arg(expr: &Expr, env: &Env) -> Atom {
    Atom::Closure(Box::new(ClosureData {
        params: Vec::new(),
        body: expr.clone(),
        env: env.clone(),
    }))
}

/// Evaluate a user-function argument according to ordinary eager rules.
pub(crate) fn eval_user_call_arg(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<Atom>, String> {
    if let Some(atom) = definition_arg_atom(expr, env) {
        Ok(vec![atom])
    } else {
        crate::eval::machine::step::run(expr, env, funcs)
    }
}

/// Evaluate a user-function argument slot according to its laziness policy.
pub(crate) fn eval_user_call_arg_slot(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    lazy: bool,
) -> Result<Vec<Atom>, String> {
    if lazy {
        Ok(vec![delayed_user_call_arg(expr, env)])
    } else {
        eval_user_call_arg(expr, env, funcs)
    }
}
