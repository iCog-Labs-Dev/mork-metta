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
        Expr::Number(number) => Atom::Num(number.clone()),
        Expr::Str(s) => Atom::str_val(s),
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

/// Single-pass, copy-on-write substitution.
/// Returns None when no variables found (no allocation, no item cloning).
/// Returns Some(new) when substitution needed — allocates only once.
///
/// Two-phase: scan for first change (no alloc), then build vec from that point.
fn subst_atom_opt(atom: &Atom, env: &Env) -> Option<Atom> {
    match atom {
        Atom::Sym(symbol) if symbol.starts_with('$') => {
            crate::eval::shared::env::lookup(env, symbol).map(|bound| {
                match &bound {
                    Atom::Sym(b) if b.as_ref() != symbol.as_ref() => {
                        subst_atom_opt(&bound, env).unwrap_or(bound)
                    }
                    _ => bound,
                }
            })
        }
        Atom::Expr(items) => {
            // Phase 1: scan for first changed child (no allocation).
            let first_change = items.iter().enumerate().find_map(|(i, item)| {
                subst_atom_opt(item, env).map(|new| (i, new))
            });
            match first_change {
                None => None, // No variables found — return unchanged.
                Some((change_idx, first_new)) => {
                    // Phase 2: build result vec. Prefix is unchanged.
                    let mut result = Vec::with_capacity(items.len());
                    result.extend_from_slice(&items[..change_idx]);
                    result.push(first_new);
                    for item in &items[change_idx + 1..] {
                        result.push(subst_atom_opt(item, env).unwrap_or_else(|| item.clone()));
                    }
                    Some(Atom::Expr(result.into()))
                }
            }
        }
        _ => None,
    }
}

pub(crate) fn subst_atom(atom: &Atom, env: &Env) -> Atom {
    if env.is_empty_env() { return atom.clone(); }
    subst_atom_opt(atom, env).unwrap_or_else(|| atom.clone())
}
