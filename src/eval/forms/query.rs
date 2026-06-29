//! Helpers for query-style evaluation.
//!
//! This module contains the logic used for user-function application,
//! including clause lookup, substitution, lazy argument handling, and
//! query-related cost behavior.

use crate::atom::Atom;
use crate::env::{Env, EnvNode};
use crate::eval::{
    machine::budget::calculate_cost,
    shared::pattern::{prepend_env, try_match_one},
};
use crate::func::Clause;
use crate::func::FnTable;
use crate::parser::{Expr, atom_to_expr, expr_to_atom};
use crate::space::Pattern;

/// Compute the total structural cost of the bindings in an environment.
pub(crate) fn env_binding_cost(env: &Env) -> i64 {
    match env.inner() {
        EnvNode::Empty => 0,
        EnvNode::Cons { value, next, .. } => {
            calculate_cost(value).unwrap_or(0) + env_binding_cost(next)
        }
        EnvNode::Link { prefix, base } => env_binding_cost(prefix) + env_binding_cost(base),
    }
}

/// Match one clause against one argument combination.
///
/// On success, this returns the environment produced by the match together
/// with the structural cost of the produced substitution.
pub(crate) fn match_clause(
    patterns: &[Expr],
    args: &[Atom],
    base_env: &Env,
    funcs: &FnTable,
) -> Option<(Env, i64)> {
    let debug_vars = std::env::var_os("MORK_DEBUG_VARCALLS").is_some();
    if patterns.len() != args.len() {
        if debug_vars {
            eprintln!(
                "debug[varcalls]: arity mismatch patterns={} args={}",
                patterns.len(),
                args.len()
            );
        }
        return None;
    }

    let mut unification_env = Env::new();
    for (pattern, arg) in patterns.iter().zip(args.iter()) {
        match try_match_one(pattern, arg, &unification_env, funcs) {
            Ok(Some(new_env)) => {
                if debug_vars {
                    eprintln!(
                        "debug[varcalls]: matched pat={} arg={} open_arg={}",
                        expr_to_atom(pattern).to_sexpr_string(),
                        arg.to_sexpr_string(),
                        arg.is_open()
                    );
                }
                unification_env = new_env;
            }
            Ok(None) => {
                if debug_vars {
                    eprintln!(
                        "debug[varcalls]: no-match pat={} arg={} open_arg={}",
                        expr_to_atom(pattern).to_sexpr_string(),
                        arg.to_sexpr_string(),
                        arg.is_open()
                    );
                }
                return None;
            }
            Err(e) => {
                if debug_vars {
                    eprintln!(
                        "debug[varcalls]: error pat={} arg={} err={}",
                        expr_to_atom(pattern).to_sexpr_string(),
                        arg.to_sexpr_string(),
                        e
                    );
                }
                return None;
            }
        }
    }

    let subst_cost = env_binding_cost(&unification_env);
    if debug_vars {
        let pats: Vec<String> = patterns
            .iter()
            .map(|p| expr_to_atom(p).to_sexpr_string())
            .collect();
        let vals: Vec<String> = args.iter().map(|a| a.to_sexpr_string()).collect();
        eprintln!(
            "debug[varcalls]: clause matched pats={} args={} subst_cost={}",
            pats.join(" | "),
            vals.join(" | "),
            subst_cost
        );
    }
    Some((prepend_env(unification_env, base_env), subst_cost))
}

/// Look up cached user-function clauses by name and arity.
///
/// Authoritative path: the derived `fn_cache`. In debug builds this also
/// shadow-runs the homoiconic space-backed lookup (`lookup_user_clauses_via_space`)
/// and asserts the two agree (α-equivalent, order-insensitive). The space path
/// is not yet on the hot path — this is the differential-verification gate
/// before it takes over (migration phases 1–2).
pub(crate) fn lookup_user_clauses(
    name: &str,
    arity: u8,
    funcs: &FnTable,
) -> Option<Vec<(Vec<Expr>, Expr)>> {
    let from_cache: Vec<(Vec<Expr>, Expr)> = {
        let cache = funcs.fn_cache.read().unwrap();
        let clauses: &Vec<Clause> = cache.get(name)?.get(&arity)?;
        clauses
            .iter()
            .map(|clause| (clause.patterns.clone(), clause.body.clone()))
            .collect()
    };

    #[cfg(debug_assertions)]
    {
        let from_space = lookup_user_clauses_via_space(name, arity, funcs).unwrap_or_default();
        let mut a: Vec<String> = from_cache.iter().map(canon_clause).collect();
        let mut b: Vec<String> = from_space.iter().map(canon_clause).collect();
        a.sort();
        b.sort();
        debug_assert_eq!(
            a, b,
            "clause-lookup divergence (fn_cache vs space) for {}/{}",
            name, arity
        );
    }

    Some(from_cache)
}

/// Phase 1: clause lookup via the homoiconic space — a parallel implementation
/// to the `fn_cache` path. Queries the trie for `(= (name $..) $body)` atoms and
/// reconstructs `(patterns, body)`. Used for shadow verification today; destined
/// to replace the `fn_cache` lookup once verified and the trie match traversal
/// is made variable-aware (migration phases 3–5).
pub(crate) fn lookup_user_clauses_via_space(
    name: &str,
    arity: u8,
    funcs: &FnTable,
) -> Option<Vec<(Vec<Expr>, Expr)>> {
    // Pattern: (= (name $ $ ... $) $body)  with `arity` argument slots.
    let mut head_pats = Vec::with_capacity(arity as usize + 1);
    head_pats.push(Pattern::Exact(Atom::sym(name)));
    for _ in 0..arity {
        head_pats.push(Pattern::Any);
    }
    let pat = Pattern::Expr(vec![
        Pattern::Exact(Atom::sym("=")),
        Pattern::Expr(head_pats),
        Pattern::Any,
    ]);

    let results = funcs.space.read().unwrap().match_atoms(&pat);
    let mut clauses = Vec::new();
    for mr in results {
        // mr.atom == (= (name p1 .. pN) body)
        let items = match &mr.atom {
            Atom::Expr(items) if items.len() == 3 => items,
            _ => continue,
        };
        if !matches!(&items[0], Atom::Sym(s) if s.as_ref() == "=") {
            continue;
        }
        let head = match &items[1] {
            Atom::Expr(h) if h.len() == arity as usize + 1 => h,
            _ => continue,
        };
        if !matches!(&head[0], Atom::Sym(s) if s.as_ref() == name) {
            continue;
        }
        let patterns: Result<Vec<Expr>, _> = head[1..].iter().map(atom_to_expr).collect();
        let body = atom_to_expr(&items[2]);
        if let (Ok(patterns), Ok(body)) = (patterns, body) {
            clauses.push((patterns, body));
        }
    }
    if clauses.is_empty() {
        None
    } else {
        Some(clauses)
    }
}

/// Canonicalize a clause to an α-equivalence-invariant string: variables are
/// renamed to `$0,$1,…` by first-occurrence order across patterns then body.
/// Lets the shadow check compare clause sets regardless of variable naming.
#[cfg(debug_assertions)]
fn canon_clause(clause: &(Vec<Expr>, Expr)) -> String {
    let mut map: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut out = String::new();
    for p in &clause.0 {
        canon_expr(p, &mut map, &mut out);
        out.push(' ');
    }
    out.push_str("=> ");
    canon_expr(&clause.1, &mut map, &mut out);
    out
}

#[cfg(debug_assertions)]
fn canon_expr(e: &Expr, map: &mut std::collections::HashMap<String, usize>, out: &mut String) {
    match e {
        Expr::Symbol(s) if s.starts_with('$') => {
            let n = map.len();
            let id = *map.entry(s.clone()).or_insert(n);
            out.push('$');
            out.push_str(&id.to_string());
        }
        // The mork encoder normalizes boolean literals to lowercase when an
        // atom round-trips through the space; fn_cache keeps source case. Fold
        // that known normalization so only structural divergences surface.
        Expr::Symbol(s) if s.eq_ignore_ascii_case("true") || s.eq_ignore_ascii_case("false") => {
            out.push_str(&s.to_ascii_lowercase())
        }
        Expr::Symbol(s) => out.push_str(s),
        Expr::Str(s) => {
            out.push('"');
            out.push_str(s);
            out.push('"');
        }
        Expr::Number(n) => out.push_str(&n.to_string()),
        Expr::List(items) => {
            out.push('(');
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                canon_expr(it, map, out);
            }
            out.push(')');
        }
    }
}
