//! Cost and budget accounting for evaluation.
//!
//! This module defines helpers for tracking and updating evaluation cost during
//! resource-bounded reduction.

use crate::atom::Atom;
use crate::env::Env;

/// A result set produced by machine evaluation.
///
/// Each result carries the produced atom together with the environment
/// associated with that result.
pub(crate) type ResultSet = Vec<(Atom, Env)>;

/// Wrap plain atoms as a result set with empty environments.
pub(crate) fn plain(atoms: Vec<Atom>) -> ResultSet {
    atoms.into_iter().map(|atom| (atom, Env::Empty)).collect()
}

/// Extract the result atoms from a result set in evaluation order.
pub(crate) fn atoms_of(results: &ResultSet) -> Vec<Atom> {
    results.iter().map(|(atom, _)| atom.clone()).collect()
}

/// Calculate the structural cost of an atom.
pub fn calculate_cost(atom: &Atom) -> Option<i64> {
    match atom {
        Atom::Sym(_) | Atom::Str(_) => Some(1),
        Atom::Num(_) => Some(1),
        Atom::Expr(items) => {
            let base_cost = (items.len() as i64) * 2;
            let recursive_cost: i64 = items.iter().filter_map(calculate_cost).sum();
            Some(base_cost + recursive_cost)
        }
        Atom::Closure(_) => Some(5),
    }
}
