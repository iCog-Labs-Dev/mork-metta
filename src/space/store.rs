//! Atomspace storage types and storage operations.

use crate::atom::Atom;
use crate::func::FnTable;

/// Return all atoms from a resolved space.
pub fn get_atoms(funcs: &FnTable, space_ref: &Atom) -> Result<Vec<Atom>, String> {
    funcs.with_resolved_space(space_ref, |space| Ok(space.get_atoms()))
}
