//! Cost and budget accounting for evaluation.
//!
//! This module defines helpers for tracking and updating evaluation cost during
//! resource-bounded reduction.

use crate::atom::Atom;
use crate::env::Env;
use crate::eval::shared::{pattern::prepend_env, subst::subst_atom};
use crate::parser::Expr;

/// A result set produced by machine evaluation.
///
/// Each result carries the produced atom together with the environment
/// associated with that result.
pub(crate) type ResultSet = Vec<(Atom, Env)>;

/// Wrap plain atoms as a result set with empty environments.
pub(crate) fn plain(atoms: Vec<Atom>) -> ResultSet {
    atoms.into_iter().map(|atom| (atom, Env::new())).collect()
}

/// Extract the result atoms from a result set in evaluation order.
pub(crate) fn atoms_of(results: &ResultSet) -> Vec<Atom> {
    results
        .iter()
        .map(|(atom, env)| subst_atom(atom, env))
        .collect()
}

/// monotone (larger terms cost more). Charging for immediate children only is a
pub fn calculate_cost(atom: &Atom) -> Option<i64> {
    match atom {
        Atom::Sym(_) | Atom::Str(_) | Atom::Num(_) => Some(1),
        Atom::Expr(items) => Some(items.len() as i64 + 1),
        Atom::Closure(_) => Some(5),
        Atom::Gnd(_) => Some(5),
    }
}

/// Calculate the structural cost of an Expr directly without allocating an Atom.
pub fn calculate_expr_cost(expr: &Expr) -> i64 {
    match expr {
        Expr::Number(_) | Expr::Symbol(_) | Expr::Str(_) => 1,
        Expr::List(items) => {
            let base_cost = (items.len() as i64) * 2;
            let recursive_cost: i64 = items.iter().map(calculate_expr_cost).sum();
            base_cost + recursive_cost
        }
    }
}

pub(crate) fn threaded_combinations(sets: &[ResultSet]) -> Vec<(Vec<Atom>, Env)> {
    // fast path for all-singleton result sets (bypasses redundant environment merging and prefix cloning)
    if sets.iter().all(|s| s.len() == 1) {
        let mut atoms = Vec::with_capacity(sets.len());
        let mut acc_env = Env::new();
        for rs in sets {
            let (atom, env) = &rs[0];
            atoms.push(atom.clone());
            acc_env = prepend_env(env.clone(), &acc_env);
        }
        return vec![(atoms, acc_env)];
    }

    let mut combos = vec![(Vec::new(), Env::new())];
    for rs in sets {
        let mut next = Vec::new();
        for (prefix, acc_env) in &combos {
            for (atom, atom_env) in rs {
                let mut atoms = prefix.clone();
                atoms.push(atom.clone());
                let merged = prepend_env(atom_env.clone(), acc_env);
                next.push((atoms, merged));
            }
        }
        combos = next;
    }
    combos
}
