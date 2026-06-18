//! Atomspace query operations.

use crate::atom::Atom;
use crate::env::Env;
use crate::func::FnTable;
use crate::parser::Expr;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;

use crate::space::core::{MatchResult, Pattern};

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
    left: &[(String, Atom)],
    right: &[(String, Atom)],
) -> Option<Vec<(String, Atom)>> {
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
                let initial_bindings: Vec<Vec<(String, Atom)>> = initial
                    .into_iter()
                    .map(|m| m.bindings)
                    .collect();

                // Each initial binding is an independent search branch for the remaining
                // subpatterns. Spawn one rayon task per initial binding — coarse-grained
                // tasks with significant work per task (the full remaining conjunction).
                // RwLock on space allows concurrent readers.
                let remaining = &subpatterns[1..];
                let results: Vec<Vec<(String, Atom)>> = if !remaining.is_empty()
                    && initial_bindings.len() > 1
                {
                    initial_bindings
                        .par_iter()
                        .map(|seed| -> Result<Vec<Vec<(String, Atom)>>, String> {
                            let mut bindings_sets = vec![seed.clone()];
                            for subpattern in remaining {
                                let mut next = Vec::new();
                                for bindings in &bindings_sets {
                                    let bound_env =
                                        crate::eval::shared::env::bind_all(env, bindings);
                                    let submatches = collect_match_results(
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
                    for subpattern in remaining {
                        let mut next = Vec::new();
                        for bindings in &bindings_sets {
                            let bound_env = crate::eval::shared::env::bind_all(env, bindings);
                            let submatches =
                                collect_match_results(funcs, space_ref, subpattern, &bound_env)?;
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
                        atom: Atom::Expr(Arc::from([Atom::sym(",")])),
                        bindings,
                    })
                    .collect());
            }
        }
    }

    let substituted = crate::eval::shared::subst::subst_expr_vars(pattern_expr, env);
    let pattern = pattern_from_expr(&substituted);
    match_in_space(funcs, space_ref, &pattern)
}

/// Evaluate a space reference expression and return its first produced atom.
pub fn eval_space_ref(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Atom, String> {
    crate::eval::machine::step::run(expr, env, funcs)?
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
            Atom::Expr(items) => {
                Atom::Expr(items.iter().map(|item| apply_subst(item, subst)).collect())
            }
            _ => atom.clone(),
        }
    }

    let atoms = crate::space::store::get_atoms(funcs, &Atom::sym("&self"))?;
    let mut out = Vec::new();
    for atom in atoms {
        if let Some(subst) = crate::eval::machine::state::unify(&atom, pattern) {
            out.push(apply_subst(replacement, &subst));
        }
    }
    Ok(out)
}
