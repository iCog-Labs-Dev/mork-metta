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
use std::sync::{Arc, OnceLock};

/// Inner node of the environment chain. Arc-wrapped by `Env` so the
/// outer clone is always O(1).
#[derive(Clone, Debug)]
pub(crate) enum EnvNode {
    /// Empty environment (no bindings).
    Empty,
    /// A binding frame: one variable mapped to an atom, linked to the
    /// outer environment.
    Cons {
        name: Arc<str>,
        value: Arc<Atom>,
        next: Env,
    },
    /// A link node prepending one environment chain onto another.
    Link {
        prefix: Env,
        base: Env,
    },
}

impl PartialEq for EnvNode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (EnvNode::Empty, EnvNode::Empty) => true,
            (
                EnvNode::Cons { name: n1, value: v1, next: nx1 },
                EnvNode::Cons { name: n2, value: v2, next: nx2 },
            ) => n1 == n2 && v1 == v2 && nx1 == nx2,
            (
                EnvNode::Link { prefix: p1, base: b1 },
                EnvNode::Link { prefix: p2, base: b2 },
            ) => p1 == p2 && b1 == b2,
            _ => false,
        }
    }
}
impl Eq for EnvNode {}

/// A lexical environment mapping variable names to atoms.
///
/// Implemented as an Arc-wrapped immutable linked list: each `extend()`
/// prepends a new binding. Lookup walks the chain from most recent to oldest.
///
/// Clone is O(1) — one atomic pointer increment — because the entire
/// chain is already shared via Arc. The prior `enum Env` (without outer Arc)
/// required copying the Cons struct (3 Arc bumps) on every frame push.
#[derive(Clone, Debug)]
pub struct Env(pub(crate) Arc<EnvNode>);

impl PartialEq for Env {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Env {}

static EMPTY_ENV: OnceLock<Env> = OnceLock::new();

const CACHE_SIZE: usize = 512;

thread_local! {
    static LOOKUP_CACHE: RefCell<[Option<(usize, String, Option<Atom>)>; CACHE_SIZE]> = const { RefCell::new([const { None }; CACHE_SIZE]) };
}

/// Clear the thread-local environment lookup cache.
pub fn clear_lookup_cache() {
    LOOKUP_CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        for slot in cache.iter_mut() {
            *slot = None;
        }
    });
}

use std::cell::RefCell;

impl Env {
    /// Create an empty environment. Returns the shared singleton (no allocation
    /// after first call — subsequent calls are a single Arc ref-count bump).
    pub fn new() -> Self {
        EMPTY_ENV.get_or_init(|| Env(Arc::new(EnvNode::Empty))).clone()
    }

    /// Access the inner node for pattern matching inside this crate.
    #[inline]
    pub(crate) fn inner(&self) -> &EnvNode {
        &self.0
    }

    /// True if this environment has no bindings.
    #[inline]
    pub fn is_empty_env(&self) -> bool {
        matches!(self.inner(), EnvNode::Empty)
    }

    /// Look up a variable by name (including the `$` prefix).
    ///
    /// Walks the linked list from the most recent binding outward.
    /// Returns `None` if the variable is not found.
    ///
    /// # Assumptions
    /// - Variable name includes the `$` prefix, e.g. `"$x"`.
    pub fn get(&self, name: &str) -> Option<Atom> {
        let _profile = crate::profile::ProfileGuard::new("Env::get");
        // ponytail: lookup cache removed because of pointer reuse/cache invalidation bugs across recursive executions.
        match self.inner() {
            EnvNode::Empty => None,
            EnvNode::Cons { name: n, value, next } => {
                if &**n == name {
                    Some((**value).clone())
                } else {
                    next.get(name)
                }
            }
            EnvNode::Link { prefix, base } => {
                prefix.get(name).or_else(|| base.get(name))
            }
        }
    }

    /// Return a new environment with one additional binding prepended.
    pub fn extend(&self, name: &str, value: Atom) -> Env {
        Env(Arc::new(EnvNode::Cons {
            name: Arc::from(name),
            value: Arc::new(value),
            next: self.clone(),
        }))
    }

    /// Return a new environment with multiple bindings prepended.
    ///
    /// Later bindings in the slice take priority — they are prepended
    /// in reverse order so the first element is checked first.
    ///
    /// # Assumptions
    /// - Each pair is `(name, value)` where name includes the `$` prefix.
    pub fn extend_all(&self, pairs: &[(Arc<str>, Arc<Atom>)]) -> Env {
        // Prepending in order gives last-pair outermost, which is correct:
        // later bindings in the slice shadow earlier ones for lookups.
        let mut env = self.clone();
        for (name, value) in pairs.iter().rev() {
            env = Env(Arc::new(EnvNode::Cons {
                name: name.clone(),
                value: value.clone(),
                next: env,
            }));
        }
        env
    }
}
