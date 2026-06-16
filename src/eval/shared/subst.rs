//! Helpers for substitution and atomization.
//!
//! This module contains utilities for expression substitution, atomization,
//! and instantiated body construction.

use crate::atom::Atom;
use crate::env::Env;
use crate::parser::{atom_to_expr, Expr};

/// Convert an expression into an atom, substituting bound variables from an
/// environment.
///
/// Unbound variables remain symbolic in the produced atom.
pub(crate) fn subst_and_atomize(expr: &Expr, env: &Env) -> Atom {
    match expr {
        Expr::Number(number) => Atom::Num(*number),
        Expr::Symbol(symbol) if symbol.starts_with('$') => {
            crate::eval::shared::env::lookup(env, symbol).unwrap_or_else(|| Atom::sym(symbol))
        }
        Expr::List(items) => Atom::Expr(items.iter().map(|item| subst_and_atomize(item, env)).collect()),
        Expr::Symbol(symbol) => Atom::sym(symbol),
    }
}

/// Substitute bound variables in an expression while preserving pattern-style
/// variable positions.
///
/// If a bound value is itself a symbolic variable name, the original variable
/// expression is retained so later matching can still treat it as a variable.
pub(crate) fn subst_expr_vars(expr: &Expr, env: &Env) -> Expr {
    match expr {
        Expr::Symbol(symbol) if symbol.starts_with('$') => {
            if let Some(atom) = crate::eval::shared::env::lookup(env, symbol) {
                match atom {
                    Atom::Sym(ref bound) if bound.starts_with('$') => {
                        // Recursive substitution: variable bound to variable
                        subst_expr_vars(&Expr::Symbol(bound.to_string()), env)
                    }
                    _ => atom_to_expr(&atom).unwrap_or_else(|_| expr.clone()),
                }
            } else {
                expr.clone()
            }
        }
        Expr::List(items) => Expr::List(items.iter().map(|item| subst_expr_vars(item, env)).collect()),
        _ => expr.clone(),
    }
}
