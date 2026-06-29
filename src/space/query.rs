//! Atomspace query operations.

use crate::atom::{Atom, expr_data};
use crate::env::Env;
use crate::eval::machine::{state::unify, step::run};
use crate::eval::shared::{
    env::{bind_all, lookup},
    subst::subst_expr_vars,
};
use crate::func::FnTable;
use crate::parser::Expr;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

use crate::space::{
    core::{MatchResult, Pattern},
    store::get_atoms,
};

/// Build a space pattern from an expression.
pub fn pattern_from_expr(expr: &Expr) -> Pattern {
    Pattern::from_expr(expr)
}

/// Return the matches for a pattern in a resolved space.
pub fn match_in_space(
    funcs: &FnTable,
    space_ref: &Atom,
    pattern: &Pattern,
) -> Result<Vec<MatchResult>, String> {
    funcs.with_resolved_space(space_ref, |space| Ok(space.match_atoms(pattern)))
}

fn merge_match_bindings(
    left: &[(Arc<str>, Arc<Atom>)],
    right: &[(Arc<str>, Arc<Atom>)],
) -> Option<Vec<(Arc<str>, Arc<Atom>)>> {
    let mut merged = left.to_vec();
    for (name, value) in right {
        if let Some((_, bound)) = merged.iter().find(|(bound_name, _)| bound_name == name) {
            if bound != value {
                return None;
            }
        } else {
            merged.push((name.clone(), value.clone()));
        }
    }
    Some(merged)
}

fn subst_pattern(pattern: &Pattern, env: &Env) -> Pattern {
    match pattern {
        Pattern::Var(name) => {
            if let Some(atom) = lookup(env, name) {
                match &atom {
                    Atom::Sym(s) if s.starts_with('$') => Pattern::Var(s.to_string()),
                    _ => Pattern::Exact(atom.clone()),
                }
            } else {
                pattern.clone()
            }
        }
        Pattern::Expr(items) => {
            let inner: Vec<Pattern> = items.iter().map(|item| subst_pattern(item, env)).collect();
            Pattern::Expr(inner)
        }
        _ => pattern.clone(),
    }
}

fn collect_match_results_pattern(
    funcs: &FnTable,
    space_ref: &Atom,
    pattern: &Pattern,
    env: &Env,
) -> Result<Vec<MatchResult>, String> {
    let substituted = subst_pattern(pattern, env);
    match_in_space(funcs, space_ref, &substituted)
}

/// Collect all matches for a surface pattern in a resolved space.
pub fn collect_match_results(
    funcs: &FnTable,
    space_ref: &Atom,
    pattern_expr: &Expr,
    env: &Env,
) -> Result<Vec<MatchResult>, String> {
    if let Expr::List(items) = pattern_expr {
        if let Some(Expr::Symbol(symbol)) = items.first() {
            if symbol == "," {
                let subpatterns = &items[1..];
                // Evaluate the first subpattern serially to get the initial binding sets.
                let initial = collect_match_results(funcs, space_ref, &subpatterns[0], env)?;
                let initial_bindings: Vec<Vec<(Arc<str>, Arc<Atom>)>> =
                    initial.into_iter().map(|m| m.bindings).collect();

                // Each initial binding is an independent search branch for the remaining
                // subpatterns. Spawn one rayon task per initial binding — coarse-grained
                // tasks with significant work per task (the full remaining conjunction).
                // RwLock on space allows concurrent readers.
                let remaining = &subpatterns[1..];
                let remaining_compiled: Vec<Pattern> =
                    remaining.iter().map(pattern_from_expr).collect();

                // ponytail: compute parallelism decision once, before allocating the vec.
                // Conditions: work must exceed thread-spawn overhead (~100μs), and we must
                // not double-parallelize when remaining subpatterns are pure space lookups
                // (those are better parallelized at the match_atoms level inside the space).
                let all_remaining_pure =
                    remaining_compiled.iter().all(|p| p.is_pure_space_lookup());
                let n_workers = rayon::current_num_threads();
                // Minimum ~8 results per thread to justify parallel dispatch overhead.
                // When all remaining subpatterns are pure space lookups, skip par_iter here —
                // match_atoms (space/core.rs) already parallelizes space traversals.
                let use_parallel = !remaining.is_empty()
                    && initial_bindings.len() > 1
                    && (initial_bindings.len() as usize) >= n_workers * 4
                    && (!all_remaining_pure || initial_bindings.len() > 256);

                let results: Vec<Vec<(Arc<str>, Arc<Atom>)>> = if use_parallel {
                    initial_bindings
                        .par_iter()
                        .map(|seed| -> Result<Vec<Vec<(Arc<str>, Arc<Atom>)>>, String> {
                            let mut bindings_sets = vec![seed.clone()];
                            for subpattern in &remaining_compiled {
                                let mut next = Vec::new();
                                for bindings in &bindings_sets {
                                    let bound_env = bind_all(env, bindings);
                                    let submatches = collect_match_results_pattern(
                                        funcs, space_ref, subpattern, &bound_env,
                                    )?;
                                    for matched in &submatches {
                                        if let Some(merged) =
                                            merge_match_bindings(bindings, &matched.bindings)
                                        {
                                            next.push(merged);
                                        }
                                    }
                                }
                                bindings_sets = next;
                                if bindings_sets.is_empty() {
                                    break;
                                }
                            }
                            Ok(bindings_sets)
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect()
                } else {
                    // Single initial binding or no remaining subpatterns: serial.
                    let mut bindings_sets = initial_bindings;
                    for subpattern in &remaining_compiled {
                        let mut next = Vec::new();
                        for bindings in &bindings_sets {
                            let bound_env = bind_all(env, bindings);
                            let submatches = collect_match_results_pattern(
                                funcs, space_ref, subpattern, &bound_env,
                            )?;
                            for matched in &submatches {
                                if let Some(merged) =
                                    merge_match_bindings(bindings, &matched.bindings)
                                {
                                    next.push(merged);
                                }
                            }
                        }
                        bindings_sets = next;
                        if bindings_sets.is_empty() {
                            break;
                        }
                    }
                    bindings_sets
                };
                return Ok(results
                    .into_iter()
                    .map(|bindings| MatchResult {
                        atom: Atom::Expr(expr_data([Atom::sym(",")])),
                        bindings,
                    })
                    .collect());
            }
        }
    }

    let substituted = subst_expr_vars(pattern_expr, env);
    let pattern = pattern_from_expr(&substituted);
    match_in_space(funcs, space_ref, &pattern)
}

/// Evaluate a space reference expression and return its first produced atom.
pub fn eval_space_ref(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Atom, String> {
    run(expr, env, funcs)?
        .into_iter()
        .next()
        .ok_or_else(|| "space expression produced no results".to_string())
}

/// Build transformed atoms for matches in the default space.
pub fn transform_matches(
    funcs: &FnTable,
    pattern: &Atom,
    replacement: &Atom,
) -> Result<Vec<Atom>, String> {
    fn apply_subst(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
        match atom {
            Atom::Sym(symbol) if symbol.starts_with('$') => subst
                .get(symbol.as_ref())
                .cloned()
                .unwrap_or_else(|| atom.clone()),
            Atom::Expr(items) => Atom::expr(
                items
                    .iter()
                    .map(|item| apply_subst(item, subst))
                    .collect::<Vec<_>>(),
            ),
            _ => atom.clone(),
        }
    }

    let atoms = get_atoms(funcs, &Atom::sym("&self"))?;
    let mut out = Vec::new();
    for atom in atoms {
        if let Some(subst) = unify(&atom, pattern) {
            out.push(apply_subst(replacement, &subst));
        }
    }
    Ok(out)
}
