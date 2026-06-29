//! Helpers for control-oriented surface forms.

use crate::atom::Atom;
use crate::env::Env;
use crate::eval::shared::env::bind;

/// Return whether an atom selects the truthy branch.
pub fn is_truthy(atom: &Atom) -> bool {
    crate::eval::shared::value::is_truthy(atom)
}

/// Extend an environment with a single binding.
pub fn bind_value(env: &Env, name: &str, value: Atom) -> Env {
    bind(env, name, value)
}
