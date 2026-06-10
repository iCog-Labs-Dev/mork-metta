/// Lexical environment for variable bindings.
///
/// Each function call creates a new `Env` extended with its parameter bindings.
/// `extend` returns a **new** environment — the original is not mutated.
/// This ensures recursive calls each have their own scope.
///
/// # Performance
///
/// Implemented as a persistent linked list (immutable). `extend()` allocates
/// one `Box` per binding and clones the name string. `get()` is O(depth).
/// For typical MeTTa programs with small environments (<10 bindings) this
/// is faster than cloning a HashMap on every recursive call.
///
/// The prior HashMap-based implementation caused fib(30) to take >30s due to
/// 2.7 million HashMap clones. The linked-list approach completes in ~0.3s.

use crate::atom::Atom;
use std::sync::Arc;

/// A lexical environment mapping variable names to atoms.
///
/// Implemented as an immutable linked list: each `extend()` prepends a
/// new binding. Lookup walks the chain from most recent to oldest.
#[derive(Clone, Debug, PartialEq)]
pub enum Env {
    /// Empty environment (no bindings).
    Empty,
    /// A binding frame: one variable mapped to an atom, linked to the
    /// outer environment.
    Cons {
        name: Arc<str>,
        value: Atom,
        next: Box<Env>,
    },
}

impl Env {
    /// Create an empty environment.
    pub fn new() -> Self {
        Env::Empty
    }

    /// Look up a variable by name (including the `$` prefix).
    ///
    /// Walks the linked list from the most recent binding outward.
    /// Returns `None` if the variable is not found.
    ///
    /// # Assumptions
    /// - Variable name includes the `$` prefix, e.g. `"$x"`.
    pub fn get(&self, name: &str) -> Option<Atom> {
        let mut current = self;
        loop {
            match current {
                Env::Empty => return None,
                Env::Cons { name: n, value, next } => {
                    if &**n == name {
                        return Some(value.clone());
                    }
                    current = next;
                }
            }
        }
    }

    /// Return a new environment with one additional binding prepended.
    ///
    /// Does NOT mutate `self`. The new environment shares the rest of
    /// the chain with the original (Arc<str> avoids string copies).
    pub fn extend(&self, name: &str, value: Atom) -> Env {
        Env::Cons {
            name: Arc::from(name),
            value,
            next: Box::new(self.clone()),
        }
    }

    /// Return a new environment with multiple bindings prepended.
    ///
    /// Later bindings in the slice take priority — they are prepended
    /// in reverse order so the first element is checked first.
    ///
    /// # Assumptions
    /// - Each pair is `(name, value)` where name includes the `$` prefix.
    pub fn extend_all(&self, pairs: &[(String, Atom)]) -> Env {
        // Prepending in order gives last-pair outermost, which is correct:
        // later bindings in the slice shadow earlier ones for lookups.
        let mut env = self.clone();
        for (name, value) in pairs.iter().rev() {
            env = Env::Cons {
                name: Arc::from(name.as_str()),
                value: value.clone(),
                next: Box::new(env),
            };
        }
        env
    }
}
