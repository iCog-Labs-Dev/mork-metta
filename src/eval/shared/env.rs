//! Helpers for environment construction and lookup.

use crate::atom::Atom;
use crate::env::{Env, EnvNode};
use std::sync::Arc;

/// Look up a bound variable in an environment.
pub fn lookup(env: &Env, name: &str) -> Option<Atom> {
    env.get(name)
}

/// Extend an environment with a single binding.
pub fn bind(env: &Env, name: &str, value: Atom) -> Env {
    env.extend(name, value)
}

/// Extend an environment with a list of bindings.
pub fn bind_all(env: &Env, bindings: &[(Arc<str>, Atom)]) -> Env {
    env.extend_all(bindings)
}

/// Prepend one environment chain onto another environment.
pub fn prepend_chain(prefix: Env, base: &Env) -> Env {
    // use Link node to link environments in O(1) time/memory without copying
    if prefix.is_empty_env() {
        base.clone()
    } else if base.is_empty_env() {
        prefix
    } else {
        Env(Arc::new(EnvNode::Link { prefix, base: base.clone() }))
    }
}
