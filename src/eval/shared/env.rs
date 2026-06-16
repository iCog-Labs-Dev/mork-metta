//! Helpers for environment construction and lookup.

use crate::atom::Atom;
use crate::env::Env;
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
pub fn bind_all(env: &Env, bindings: &[(String, Atom)]) -> Env {
    env.extend_all(bindings)
}

/// Prepend one environment chain onto another environment.
pub fn prepend_chain(prefix: Env, base: &Env) -> Env {
    match prefix {
        Env::Empty => base.clone(),
        Env::Cons {
            name,
            value,
            next,
        } => {
            let inner = next.as_ref().clone();
            Env::Cons {
                name,
                value,
                next: Arc::new(prepend_chain(inner, base)),
            }
        }
    }
}
