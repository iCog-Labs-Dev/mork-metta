//! Helpers for inspecting evaluator values.

use crate::atom::Atom;

/// Return whether an atom is truthy.
pub fn is_truthy(atom: &Atom) -> bool {
    atom.is_truthy()
}

/// Return a numeric value from an atom.
pub fn expect_num(atom: &Atom) -> Result<i128, String> {
    atom.as_num()
}

/// Return a symbol string from an atom.
pub fn expect_sym(atom: &Atom) -> Result<&str, String> {
    atom.as_sym()
}

/// Return expression items from an atom.
pub fn expect_expr(atom: &Atom) -> Result<&[Atom], String> {
    atom.as_expr()
}
