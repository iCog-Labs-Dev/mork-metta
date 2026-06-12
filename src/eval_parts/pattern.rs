/// Pattern matching for multi-clause functions.
///
/// Provides the building blocks for matching argument values against
/// clause patterns: literal matching, non-linear pattern (re-binding),
/// and structural destructuring for nested lists.
///
/// # Semantics
///
/// All pattern-matching functions create a **fresh** environment for each
/// match attempt, so outer bindings in the calling environment never
/// interfere with variable capture during recursive calls. The returned
/// environment is then merged with the caller's via [`prepend_env`].

use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::core::eval;
use crate::func::{Clause, FnTable};
use std::sync::Arc;
use crate::parser::Expr;

/// Try to match argument atoms against a clause's patterns.
///
/// Uses a fresh environment for pattern matching (so outer bindings don't
/// interfere with variable capture in recursive calls). On success, extends
/// the calling `env` with the matched bindings.
///
/// Returns `Some(env)` with the extended environment if the pattern matches,
/// or `None` if this clause doesn't match (try the next one).
///
/// # Errors
/// Returns `Err` only on genuine errors (not on pattern mismatch).
pub(crate) fn try_match_clause(
    patterns: &[Expr],
    args: &[Atom],
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    if patterns.len() != args.len() {
        return Ok(None);
    }
    // Use a fresh env for pattern matching so outer bindings don't interfere
    // with variable capture in recursive calls (e.g., fib($N) called with
    // outer $N=30 should match $N=29, not fail).
    let mut match_env = Env::new();
    for (pat, arg) in patterns.iter().zip(args.iter()) {
        match try_match_one(pat, arg, &match_env, funcs)? {
            Some(new_env) => match_env = new_env,
            None => return Ok(None),
        }
    }
    // Splice match_env (built on Empty) onto the calling env without converting
    // to Vec<(String, Atom)> — avoids Arc<str>→String→Arc<str> round-trips.
    Ok(Some(prepend_env(match_env, env)))
}

/// Walk `match_env` (a chain built on top of Env::Empty) and replace the
/// Empty terminus with `base`, merging the two chains without any String
/// allocations — Arc<str> name references are reused as-is.
pub(crate) fn prepend_env(match_env: Env, base: &Env) -> Env {
    match match_env {
        Env::Empty => base.clone(),
        Env::Cons { name, value, next } => {
            let inner = Arc::try_unwrap(next).unwrap_or_else(|arc| (*arc).clone());
            Env::Cons {
                name,
                value,
                next: Arc::new(prepend_env(inner, base)),
            }
        },
    }
}

/// Match a single pattern against a single atom.
///
/// Pattern kinds:
/// - `$var` (symbol starting with `$`): binds to the atom, or checks
///   equality if already bound (non-linear patterns).
/// - `Num(n)`: matches only `Atom::Num(n)`.
/// - `Sym(s)`: matches only `Atom::Sym(t)` where `s == t`.
/// - `List(items)`: structural match — recursively matches each element.
pub(crate) fn try_match_one(
    pattern: &Expr,
    atom: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    match pattern {
        Expr::Symbol(s) if s.starts_with('$') => {
            // Variable pattern: bind if unbound, check equality if bound
            match env.get(s) {
                Some(bound) if &bound != atom => Ok(None),
                _ => Ok(Some(env.extend(s, atom.clone()))),
            }
        }
        Expr::Number(n) => match atom {
            Atom::Num(m) if n == m => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal number.
            Atom::Sym(s) if s.starts_with('$') => Ok(Some(env.extend(s, Atom::Num(*n)))),
            _ => Ok(None),
        },
        Expr::Symbol(s) => match atom {
            // Normalize through Atom::sym() so "True"/"False" patterns match lowercase atoms.
            Atom::Sym(t) if Atom::sym(s) == Atom::Sym(t.clone()) => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal symbol.
            Atom::Sym(v) if v.starts_with('$') => Ok(Some(env.extend(v, Atom::sym(s)))),
            _ => Ok(None),
        },
        Expr::List(items) => match atom {
            Atom::Expr(elems) => {
                if items.len() != elems.len() {
                    return Ok(None);
                }
                let mut current = env.clone();
                for (pat, arg) in items.iter().zip(elems.iter()) {
                    match try_match_one(pat, arg, &current, funcs)? {
                        Some(new_env) => current = new_env,
                        None => return Ok(None),
                    }
                }
                Ok(Some(current))
            }
            // Free variable: evaluate the List pattern as code (computation
            // in pattern, e.g. `(if (== $x 2) 43 44)`) and bind the result.
            Atom::Sym(s) if s.starts_with('$') => {
                let expr = Expr::List(items.clone());
                match eval(&expr, env, funcs) {
                    Ok(mut results) => match results.next() {
                        Some(val) => Ok(Some(env.extend(s, val))),
                        None => Ok(None),
                    },
                    Err(_) => Ok(None),
                }
            }
            _ => Ok(None),
        },
    }
}

/// Try every clause against `arg_vals`, returning `(match_env, &Clause)` for
/// each match.  This is the single call-site for `try_match_clause` across
/// both `call_with_ref` and `eval_constrained`, ensuring the two dispatch paths
/// can never diverge in their clause-selection logic.
///
/// `base_env` controls what outer variables are visible during matching:
/// - pass the calling `env` in `call_with_ref` (outer bindings in scope),
/// - pass `&Env::new()` in `eval_constrained` (isolates new bindings for accumulation).
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
