//! Helpers for pattern matching.
//!
//! This module contains reusable pattern-matching functions used for query,
//! destructuring, and binding.

use crate::atom::Atom;
use crate::env::Env;
use crate::func::{Clause, FnTable};
use crate::parser::Expr;

/// Match a clause's argument patterns against evaluated argument atoms.
///
/// Returns the extended environment when every pattern matches its
/// corresponding argument. If any pattern does not match, this function
/// returns `Ok(None)`.
pub(crate) fn try_match_clause(
    patterns: &[Expr],
    args: &[Atom],
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    if patterns.len() != args.len() {
        return Ok(None);
    }

    let mut match_env = Env::new();
    for (pattern, arg) in patterns.iter().zip(args.iter()) {
        match try_match_one(pattern, arg, &match_env, funcs)? {
            Some(new_env) => match_env = new_env,
            None => return Ok(None),
        }
    }

    Ok(Some(prepend_env(match_env, env)))
}

/// Prepend one environment chain onto another environment.
///
/// The bindings stored in `match_env` remain in front of `base`, preserving the
/// existing binding order inside `match_env`.
pub(crate) fn prepend_env(match_env: Env, base: &Env) -> Env {
    crate::eval::shared::env::prepend_chain(match_env, base)
}

/// Match a single pattern against a single atom.
///
/// Variables bind on first occurrence and compare structurally on later
/// occurrences. Lists match expression atoms structurally, with special support
/// for `(cons head tail)` destructuring against non-empty expression atoms.
pub(crate) fn try_match_one(
    pattern: &Expr,
    atom: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    match pattern {
    Expr::Symbol(symbol) if symbol.starts_with('$') => match crate::eval::shared::env::lookup(env, symbol) {
            Some(bound) if bound == *atom => Ok(Some(env.clone())),
            Some(_) => Ok(None),
            None => Ok(Some(crate::eval::shared::env::bind(
                env,
                symbol,
                atom.clone(),
            ))),
        },
        Expr::Number(number) => match atom {
            Atom::Num(value) if number == value => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal number.
            Atom::Sym(var_name) if var_name.starts_with('$') => {
                let key: &str = var_name.as_ref();
                match crate::eval::shared::env::lookup(env, key) {
                    Some(bound) if Atom::Num(*number) == bound => Ok(Some(env.clone())),
                    Some(_) => Ok(None),
                    None => Ok(Some(crate::eval::shared::env::bind(
                        env,
                        key,
                        Atom::Num(*number),
                    ))),
                }
            }
            _ => Ok(None),
        },
        Expr::Symbol(symbol) => match atom {
            // Exact canonicalized match
            Atom::Sym(value)
                if Atom::sym(symbol.as_str()) == Atom::Sym(value.clone()) =>
            {
                Ok(Some(env.clone()))
            }
            // Atom is an unbound call-site variable ($x) against a ground pattern
            // ("False") — bind $x to the pattern value (bidirectional unification)
            Atom::Sym(var_name) if var_name.starts_with('$') => {
                let key: &str = var_name.as_ref();
                match crate::eval::shared::env::lookup(env, key) {
                    Some(bound) if Atom::sym(symbol.as_str()) == bound => Ok(Some(env.clone())),
                    Some(_) => Ok(None),
                    None => Ok(Some(crate::eval::shared::env::bind(
                        env,
                        key,
                        Atom::sym(symbol),
                    ))),
                }
            }
            _ => Ok(None),
        },
        Expr::List(items) => {
            if items.len() == 3
                && matches!(&items[0], Expr::Symbol(head) if head == "cons")
            {
                return match atom {
                    Atom::Expr(elements) if !elements.is_empty() => {
                        let Some(head_env) = try_match_one(&items[1], &elements[0], env, funcs)?
                        else {
                            return Ok(None);
                        };
                        let tail = Atom::Expr(elements[1..].to_vec());
                        try_match_one(&items[2], &tail, &head_env, funcs)
                    }
                    _ => Ok(None),
                };
            }

            match atom {
                Atom::Expr(elements) if items.len() == elements.len() => {
                    let mut current = env.clone();
                    for (subpattern, element) in items.iter().zip(elements.iter()) {
                        match try_match_one(subpattern, element, &current, funcs)? {
                            Some(new_env) => current = new_env,
                            None => return Ok(None),
                        }
                    }
                    Ok(Some(current))
                }
                Atom::Sym(symbol) if symbol.starts_with('$') => {
                let expr = Expr::List(items.clone());
                match crate::eval::machine::step::run(&expr, env, funcs) {
                    Ok(results) => match results.into_iter().next() {
                        Some(value) => Ok(Some(crate::eval::shared::env::bind(
                            env,
                            symbol,
                            value,
                        ))),
                            None => Ok(None),
                        },
                        Err(_) => Ok(None),
                    }
                }
                _ => Ok(None),
            }
        }
    }
}

/// Match every clause against a list of argument atoms.
///
/// Each successful match returns the environment produced by matching together
/// with the clause that matched.
pub(crate) fn match_clauses<'c>(
    clauses: &'c [Clause],
    arg_vals: &[Atom],
    base_env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Env, &'c Clause)>, String> {
    let mut matched = Vec::new();
    for clause in clauses {
        if let Some(env) = try_match_clause(&clause.patterns, arg_vals, base_env, funcs)? {
            matched.push((env, clause));
        }
    }
    Ok(matched)
}
