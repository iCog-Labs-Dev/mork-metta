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
use std::sync::{Arc, LazyLock, OnceLock};

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

static EMPTY_ENV: LazyLock<Env> = LazyLock::new(|| Env(Arc::new(EnvNode::Empty)));

const CACHE_SIZE: usize = 512;

thread_local! {
    static LOOKUP_CACHE: std::cell::RefCell<[Option<(usize, String, Option<Atom>)>; CACHE_SIZE]> =
        const { std::cell::RefCell::new([const { None }; CACHE_SIZE]) };
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

impl Env {
    /// Create an empty environment. Returns the shared singleton (no allocation
    /// after first call — subsequent calls are a single Arc ref-count bump).
    pub fn new() -> Self {
        EMPTY_ENV.clone()
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
        let mut curr = self.clone();
        // explicit stack for iterative traversal of Link chains
        // instead of C-stack recursion, avoiding stack overflow on deep chains.
        let mut todo: Vec<Env> = Vec::new();
        loop {
            match curr.inner() {
                EnvNode::Empty => {
                    curr = todo.pop()?;
                    continue;
                }
                EnvNode::Cons { name: n, value, next } => {
                    if &**n == name {
                        return Some((**value).clone());
                    }
                    curr = next.clone();
                }
                EnvNode::Link { prefix, base } => {
                    todo.push(base.clone());
                    curr = prefix.clone();
                }
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

    /// Filter out bindings of names in `skip_names` that were added on top of `boundary`.
    pub fn clean_and_merge(&self, boundary: &Env, skip_names: &[String]) -> Env {
        let mut bindings = Vec::new();
        self.collect_new_bindings(boundary, skip_names, &mut bindings);

        let mut res = boundary.clone();
        for (name, value) in bindings.into_iter().rev() {
            res = Env(Arc::new(EnvNode::Cons {
                name,
                value,
                next: res,
            }));
        }
        res
    }

    /// Collect bindings added above `boundary`, then walk `prefix` chains
    /// iteratively via an explicit worklist instead of C-stack recursion.
    fn collect_new_bindings(
        &self,
        boundary: &Env,
        skip_names: &[String],
        bindings: &mut Vec<(Arc<str>, Arc<Atom>)>,
    ) {
        // worklist flattens Link chains iteratively.
        // For a chain of N Link nodes the Vec grows to at most N (bounds to function call depth).
        let mut worklist: Vec<Env> = Vec::new();
        let mut curr = self.clone();
        loop {
            if Arc::ptr_eq(&curr.0, &boundary.0) {
                // This branch done, try the next from the worklist
                if let Some(next) = worklist.pop() {
                    curr = next;
                    continue;
                }
                return;
            }
            match &*curr.0 {
                EnvNode::Empty => {
                    if let Some(next) = worklist.pop() {
                        curr = next;
                        continue;
                    }
                    return;
                }
                EnvNode::Cons { name, value, next } => {
                    let skip = skip_names.iter().any(|s| s.as_str() == &**name);
                    if !skip {
                        bindings.push((name.clone(), value.clone()));
                    }
                    curr = next.clone();
                }
                EnvNode::Link { prefix, base } => {
                    worklist.push(base.clone());
                    curr = prefix.clone();
                }
            }
        }
    }

    /// Collect all bindings from this environment, walking `Link` chains
    /// iteratively via an explicit worklist instead of C-stack recursion.
    fn collect_all_bindings(
        &self,
        skip_names: &[String],
        bindings: &mut Vec<(Arc<str>, Arc<Atom>)>,
    ) {
        // worklist flattens Link chains iteratively.
        let mut worklist: Vec<Env> = Vec::new();
        let mut curr = self.clone();
        loop {
            if curr.is_empty_env() {
                if let Some(next) = worklist.pop() {
                    curr = next;
                    continue;
                }
                return;
            }
            match &*curr.0 {
                EnvNode::Empty => {
                    if let Some(next) = worklist.pop() {
                        curr = next;
                        continue;
                    }
                    return;
                }
                EnvNode::Cons { name, value, next } => {
                    let skip = skip_names.iter().any(|s| s.as_str() == &**name);
                    if !skip {
                        bindings.push((name.clone(), value.clone()));
                    }
                    curr = next.clone();
                }
                EnvNode::Link { prefix, base } => {
                    worklist.push(base.clone());
                    curr = prefix.clone();
                }
            }
        }
    }
}
