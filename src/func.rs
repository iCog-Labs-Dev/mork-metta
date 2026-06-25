use crate::atom::Atom;
use crate::parser::Expr;
use crate::space::Space;
use rustc_hash::FxHashMap as HashMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
/// Function dispatch table.
///
/// Stores both user-defined functions (compiled from `(= ...)` forms) and
/// native (grounded) Rust functions. Also owns the atom space reference and
/// mutable state store for space/state operations.
///
/// # Thread safety
/// `FnTable` is `Send + Sync`:
/// - `map` uses `RwLock` — concurrent reads during eval, exclusive writes at load time.
/// - `space`, `state`, `import_dir` use `Mutex` — serialised access, no `Sync` required
///   from the Space implementors (which may use `Cell` internally, e.g. MorkSpace).
/// - `FunctionKind::Native` requires `Send + Sync` on the function pointer so that
///   native closures registered at startup are safe to call from worker threads.
use std::sync::{Arc, Mutex, RwLock};

/// An iterator over nondeterministic results from evaluation.
///
/// Allocates a `Box` only for multi-result streams. The common case of
/// a single result uses the stack-allocated `Single` variant — zero heap
/// allocation.
pub enum NDet {
    Single(Option<Atom>),
    Stream(Box<dyn Iterator<Item = Atom> + Send>),
}
impl NDet {
    pub fn single(atom: Atom) -> Self {
        NDet::Single(Some(atom))
    }
    pub fn stream(iter: impl Iterator<Item = Atom> + Send + 'static) -> Self {
        NDet::Stream(Box::new(iter))
    }
}
impl Iterator for NDet {
    type Item = Atom;
    fn next(&mut self) -> Option<Atom> {
        match self {
            NDet::Single(opt) => opt.take(),
            NDet::Stream(iter) => iter.next(),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            NDet::Single(opt) => (if opt.is_some() { 1 } else { 0 }, Some(1)),
            NDet::Stream(iter) => iter.size_hint(),
        }
    }
}

/// A single clause of a multi-clause (pattern-matching) user-defined function.
/// Kept for compile_definition return type and conversion to space atoms.
#[derive(Clone, Debug, PartialEq)]
pub struct Clause {
    pub patterns: Vec<Expr>,
    pub body: Expr,
}

#[derive(Clone)]
pub enum FunctionKind {
    Native {
        // REASON: Arc<dyn Fn + Send + Sync> allows closures captured at startup to be
        // called safely from parallel worker threads.
        func: Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>,
    },
}

/// A named function in the table. Only Native Rust closures remain.
/// User-defined (= ...) functions are looked up from the space directly.
#[derive(Clone)]
pub struct Function {
    pub name: String,
    pub kind: FunctionKind,
    pub effect: Effect,
}

/// Declares what kind of knowledge-base access a native function performs.
/// Aligned to the MeTTa spec's structural rule distinction:
///   - QUERY (match) reads `k` but doesn't mutate it  → SpaceRead
///   - ADDATOM / REMATOM mutate `k`                   → SpaceMutate
///   - Arithmetic / control / pure rewriting           → Pure
///
/// Used for memoization decisions, parallelism guards, and transitively
/// propagating purity through user-defined functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    /// No KB access. Safe to memoize and run in parallel branches.
    Pure,
    /// Reads KB (e.g. match). Safe to parallelize; memoizable only with stamp guard.
    SpaceRead,
    /// Mutates KB (add-atom, remove-atom) or performs IO. Neither memoizable nor parallelizable.
    SpaceMutate,
}

impl Effect {
    /// Return the more restrictive of two effects (Pure < SpaceRead < SpaceMutate).
    pub fn max(self, other: Effect) -> Effect {
        match (self, other) {
            (Effect::SpaceMutate, _) | (_, Effect::SpaceMutate) => Effect::SpaceMutate,
            (Effect::SpaceRead, _) | (_, Effect::SpaceRead) => Effect::SpaceRead,
            _ => Effect::Pure,
        }
    }
}

/// Two-level function map: name → (arity → Function).
type FuncMap = HashMap<String, HashMap<u8, Arc<Function>>>;

pub struct FnTable {
    /// Read-heavy: many concurrent lookups during eval, writes only at load time.
    map: RwLock<FuncMap>,
    /// Atom storage — RwLock allows concurrent readers (queries), exclusive writers (add/remove).
    pub space: RwLock<Box<dyn Space + Send + Sync>>,
    /// Lazily-created named spaces addressed by `&name`.
    pub named_spaces: RwLock<HashMap<String, Box<dyn Space + Send + Sync>>>,
    /// Mutable state store for `get-state`, `change-state!`, `bind!`.
    pub state: Mutex<HashMap<String, Atom>>,
    /// Function definition cache — populated from space at reify time, updated
    /// on add-atom/remove-atom. Read-heavy (every function dispatch), so RwLock.
    pub fn_cache: RwLock<HashMap<String, HashMap<u8, Vec<Clause>>>>,
    /// Space-free purity of each user function, computed at definition time and
    /// recomputed on redefinition (self-evolution-stable). Drives the *only*
    /// sound parallelization decision: a function is parallel-safe iff it (and
    /// everything it calls) performs no space access and no IO. Absent ⇒ impure.
    pub fn_effect: RwLock<HashMap<String, HashMap<u8, Effect>>>,
    /// Directory of the file currently being loaded (load-time only).
    pub import_dir: Mutex<PathBuf>,
    /// Incremented on every add-atom/remove-atom. Memo cache entries tagged
    /// with a stale stamp are evicted, making memoization self-evolution-safe.
    pub memo_stamp: AtomicU64,
    /// Memo cache for pure user-defined functions: (name, args) → (stamp, results).
    pub memo_cache: RwLock<HashMap<(String, Vec<Atom>), (u64, Vec<Atom>)>>,
    /// Lazy-arg mask cache: (name, arity) → Vec<bool>. Populated on first call,
    /// invalidated on cache_fn (add-atom / redefinition).
    pub lazy_mask_cache: RwLock<HashMap<(String, u8), Vec<bool>>>,
}

impl FnTable {
    pub fn new() -> Self {
        FnTable {
            map: RwLock::new(HashMap::default()),
            space: RwLock::new(Box::new(crate::space::MorkSpace::new())),
            named_spaces: RwLock::new(HashMap::default()),
            fn_cache: RwLock::new(HashMap::default()),
            fn_effect: RwLock::new(HashMap::default()),
            state: Mutex::new(HashMap::default()),
            import_dir: Mutex::new(PathBuf::from(".")),
            memo_stamp: AtomicU64::new(0),
            memo_cache: RwLock::new(HashMap::default()),
            lazy_mask_cache: RwLock::new(HashMap::default()),
        }
    }

    pub fn with_space(space: Box<dyn Space + Send>) -> Self {
        FnTable {
            map: RwLock::new(HashMap::default()),
            space: RwLock::new(space),
            named_spaces: RwLock::new(HashMap::default()),
            fn_cache: RwLock::new(HashMap::default()),
            fn_effect: RwLock::new(HashMap::default()),
            state: Mutex::new(HashMap::default()),
            import_dir: Mutex::new(PathBuf::from(".")),
            memo_stamp: AtomicU64::new(0),
            memo_cache: RwLock::new(HashMap::default()),
            lazy_mask_cache: RwLock::new(HashMap::default()),
        }
    }

    pub fn insert_native<F>(&self, name: &str, arity: u8, func: F)
    where
        F: Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static,
    {
        self.map
            .write()
            .unwrap()
            .entry(name.to_string())
            .or_insert_with(HashMap::default)
            .insert(
                arity,
                Arc::new(Function {
                    name: name.to_string(),
                    kind: FunctionKind::Native {
                        func: Arc::new(func),
                    },
                    effect: Effect::SpaceMutate,
                }),
            );
    }

    pub fn mark_pure(&self, name: &str, arity: u8) {
        if let Some(arc_func) = self
            .map
            .write()
            .unwrap()
            .get_mut(name)
            .and_then(|inner| inner.get_mut(&arity))
            .and_then(|a| Arc::get_mut(a))
        {
            arc_func.effect = Effect::Pure;
        }
    }

    pub fn has(&self, name: &str, arity: u8) -> bool {
        self.map
            .read()
            .unwrap()
            .get(name)
            .map_or(false, |inner| inner.contains_key(&arity))
    }

    pub fn has_greater_arity(&self, name: &str, arity: u8) -> bool {
        // ponytail: check if function is registered with any arity greater than current arity
        if self.map.read().unwrap().get(name).map_or(false, |inner| inner.keys().any(|&k| k > arity)) {
            return true;
        }
        if self.fn_cache.read().unwrap().get(name).map_or(false, |inner| inner.keys().any(|&k| k > arity)) {
            return true;
        }
        false
    }

    pub fn is_registered(&self, name: &str) -> bool {
        self.map.read().unwrap().contains_key(name) || self.fn_cache.read().unwrap().contains_key(name)
    }

    pub fn get(&self, name: &str, arity: u8) -> Option<Arc<Function>> {
        // thread-local 4-element LRU cache to bypass costly RwLock read locks during recursive dispatch
        thread_local! {
            static CACHE: std::cell::RefCell<Vec<(String, u8, Option<Arc<Function>>)>> = std::cell::RefCell::new(Vec::with_capacity(4));
        }

        let cached = CACHE.with(|c| {
            let mut cache = c.borrow_mut();
            if let Some(pos) = cache.iter().position(|(n, a, _)| n == name && *a == arity) {
                let entry = cache[pos].clone();
                if pos > 0 {
                    cache.remove(pos);
                    cache.insert(0, entry.clone());
                }
                return Some(entry.2);
            }
            None
        });

        if let Some(res) = cached {
            return res;
        }

        let res = self.map
            .read()
            .unwrap()
            .get(name)
            .and_then(|inner| inner.get(&arity))
            .cloned();

        CACHE.with(|c| {
            let mut cache = c.borrow_mut();
            if cache.len() >= 4 {
                cache.pop();
            }
            cache.insert(0, (name.to_string(), arity, res.clone()));
        });

        res
    }

    pub fn with_resolved_space<R>(
        &self,
        space_ref: &Atom,
        f: impl FnOnce(&dyn Space) -> Result<R, String>,
    ) -> Result<R, String> {
        match space_ref {
            Atom::Sym(name) if name.as_ref() == "&self" => {
                let space = self.space.read().unwrap();
                f(space.as_ref())
            }
            Atom::Sym(name) if name.starts_with('&') => {
                // Fast path: space already exists — read lock only (concurrent readers).
                {
                    let spaces = self.named_spaces.read().unwrap();
                    if let Some(space) = spaces.get(name.as_ref()) {
                        return f(space.as_ref());
                    }
                }
                // Slow path: lazily create the space — write lock.
                let mut spaces = self.named_spaces.write().unwrap();
                let space = spaces.entry(name.to_string()).or_insert_with(|| {
                    Box::new(crate::space::MorkSpace::new()) as Box<dyn Space + Send + Sync>
                });
                f(space.as_ref())
            }
            other => Err(format!(
                "expected space reference, got {}",
                other.to_sexpr_string()
            )),
        }
    }

    /// Get or compute the lazy-arg mask for a user function (cached per name+arity).
    pub fn get_lazy_mask(&self, name: &str, arity: u8) -> Vec<bool> {
        let key = (name.to_string(), arity);
        if let Some(mask) = self.lazy_mask_cache.read().unwrap().get(&key) {
            return mask.clone();
        }
        let mask = if let Some(clauses) = self.fn_cache.read().unwrap()
            .get(name).and_then(|m| m.get(&arity))
        {
            let slice: Vec<(&[crate::parser::Expr], &crate::parser::Expr)> =
                clauses.iter().map(|c| (c.patterns.as_slice(), &c.body)).collect();
            crate::eval::shared::closure::lazy_user_arg_mask(&slice)
        } else {
            vec![]
        };
        self.lazy_mask_cache.write().unwrap().insert(key, mask.clone());
        mask
    }

    pub fn cache_fn(&self, name: &str, arity: u8, clause: Clause) {
        // Invalidate lazy mask when clauses change.
        self.lazy_mask_cache.write().unwrap().remove(&(name.to_string(), arity));
        // Compute space-free purity BEFORE taking the cache write lock: the
        // analysis reads fn_cache/fn_effect, so locking first would deadlock.
        // Self-recursion is optimistically pure, so directly recursive pure
        // functions (e.g. fib) stay parallelizable.
        let clause_effect =
            is_pure_expr_assuming(&clause.body, self, name);

        {
            let mut cache = self.fn_cache.write().unwrap();
            let clauses = cache
                .entry(name.to_string())
                .or_insert_with(HashMap::default)
                .entry(arity)
                .or_insert_with(Vec::new);
            // Idempotent: the trie gives `(= head body)` set semantics, so the
            // dispatch cache must too — re-adding an identical clause must not
            // duplicate it and double the result multiset (already counted in
            // purity, so skip the update too).
            if clauses.contains(&clause) {
                return;
            }
            clauses.push(clause);
        }

        // Most restrictive clause wins: SpaceMutate beats SpaceRead beats Pure.
        let mut effects = self.fn_effect.write().unwrap();
        let entry = effects
            .entry(name.to_string())
            .or_insert_with(HashMap::default)
            .entry(arity)
            .or_insert(Effect::Pure);
        *entry = entry.max(clause_effect);
    }

    pub fn uncache_fn(&self, name: &str, arity: u8) {
        if let Some(inner) = self.fn_cache.write().unwrap().get_mut(name) {
            inner.remove(&arity);
        }
        if let Some(inner) = self.fn_effect.write().unwrap().get_mut(name) {
            inner.remove(&arity);
        }
    }

    /// Check if the given name has a function registered at a higher arity than `given`.
    pub fn has_higher_arity(&self, name: &str, given: usize) -> bool {
        // Check native functions
        if let Some(inner) = self.map.read().unwrap().get(name) {
            if inner.keys().any(|&a| a as usize > given) {
                return true;
            }
        }
        // Check user functions
        if let Some(inner) = self.fn_cache.read().unwrap().get(name) {
            if inner.keys().any(|&a| a as usize > given) {
                return true;
            }
        }
        false
    }

    /// Bump the mutation stamp. Call on every add-atom / remove-atom so that
    /// memo cache entries from before the mutation are treated as stale.
    pub fn bump_memo_stamp(&self) {
        self.memo_stamp.fetch_add(1, Ordering::Relaxed);
    }

    /// Look up a memoized result. Returns `Some(results)` only when the entry
    /// exists AND was stored under the current mutation stamp.
    pub fn memo_get(&self, key: &(String, Vec<Atom>)) -> Option<Vec<Atom>> {
        let stamp = self.memo_stamp.load(Ordering::Relaxed);
        self.memo_cache
            .read()
            .unwrap()
            .get(key)
            .filter(|(s, _)| *s == stamp)
            .map(|(_, v)| v.clone())
    }

    /// Store a memoized result tagged with the current mutation stamp.
    pub fn memo_set(&self, key: (String, Vec<Atom>), result: Vec<Atom>) {
        if result
            .iter()
            .any(crate::eval::shared::fresh::contains_fresh_vars)
        {
            return;
        }
        let stamp = self.memo_stamp.load(Ordering::Relaxed);
        self.memo_cache.write().unwrap().insert(key, (stamp, result));
    }

    /// True if the named function at the given arity is marked pure.
    /// Return the registered Effect for a native function, or None if not found.
    pub fn effect_of(&self, name: &str, arity: u8) -> Option<Effect> {
        self.get(name, arity).map(|f| f.effect)
    }

    pub fn is_pure_fn(&self, name: &str, arity: u8) -> bool {
        self.fn_effect
            .read()
            .unwrap()
            .get(name)
            .and_then(|m: &HashMap<u8, Effect>| m.get(&arity))
            .copied()
            .map(|e| e == Effect::Pure)
            .unwrap_or(false)
    }

    /// Check if a named function is pure at the given arity.
    /// Returns `false` if the function is not found (conservative).
    pub fn is_pure(&self, name: &str, arity: u8) -> bool {
        // Native builtins carry an authoritative space-free purity flag.
        if let Some(inner) = self.map.read().unwrap().get(name) {
            if let Some(f) = inner.get(&arity) {
                return f.effect == Effect::Pure;
            }
        }
        // User-defined functions: purity computed at definition time (sound and
        // self-evolution-stable). Unknown symbols and defs added directly to the
        // space are treated as impure — never parallelized on an unproven
        // assumption. (A cache miss still dispatches correctly via the space
        // fallback; it just runs sequentially.)
        self.fn_effect
            .read()
            .unwrap()
            .get(name)
            .and_then(|inner| inner.get(&arity))
            .copied()
            .map(|e| e == Effect::Pure)
            .unwrap_or(false)
    }

    /// True if this function is safe to run in parallel (Pure or SpaceRead).
    pub fn is_parallelizable(&self, name: &str, arity: u8) -> bool {
        if let Some(inner) = self.map.read().unwrap().get(name) {
            if let Some(f) = inner.get(&arity) {
                return f.effect != Effect::SpaceMutate;
            }
        }
        self.fn_effect
            .read()
            .unwrap()
            .get(name)
            .and_then(|inner| inner.get(&arity))
            .copied()
            .map(|e| e != Effect::SpaceMutate)
            .unwrap_or(false)
    }

    /// True if the expression can be evaluated in parallel (no space mutation).
    pub fn is_parallelizable_expr(&self, expr: &crate::parser::Expr) -> bool {
        is_pure_expr_inner(expr, self, None) != Effect::SpaceMutate
    }

    /// Estimate the computational weight of an expression.
    pub fn expr_weight(&self, expr: &crate::parser::Expr) -> usize {
        use crate::parser::Expr;
        match expr {
            Expr::Number(_) | Expr::Symbol(_) | Expr::Str(_) => 0,
            Expr::List(items) => {
                if items.is_empty() {
                    return 0;
                }
                let mut weight = 1;
                for item in items.iter() {
                    weight += self.expr_weight(item);
                }
                if let Expr::Symbol(head) = &items[0] {
                    match head.as_str() {
                        "quote" | "|->" | "empty" => {}
                        "if" | "progn" | "prog1" | "let" | "let*" | "chain" | "collapse" | "once" | "superpose" => {
                            weight += 10;
                        }
                        _ => {
                            weight += 15;
                        }
                    }
                } else {
                    weight += 15;
                }
                weight
            }
        }
    }
}

fn is_pure_expr_assuming(expr: &crate::parser::Expr, funcs: &FnTable, self_name: &str) -> Effect {
    is_pure_expr_inner(expr, funcs, Some(self_name))
}

fn is_pure_expr_inner(
    expr: &crate::parser::Expr,
    funcs: &FnTable,
    assume_pure: Option<&str>,
) -> Effect {
    use crate::parser::Expr;
    match expr {
        Expr::Number(_) | Expr::Symbol(_) | Expr::Str(_) => Effect::Pure,
        Expr::List(items) if items.is_empty() => Effect::Pure,
        Expr::List(items) => {
            let args_effect =
                || items[1..].iter()
                    .map(|e| is_pure_expr_inner(e, funcs, assume_pure))
                    .fold(Effect::Pure, Effect::max);
            if let Expr::Symbol(s) = &items[0] {
                // Dispatch-level special forms not in the fn table.
                match s.as_str() {
                    // Unconditionally pure: never evaluate their argument or body.
                    "quote" | "|->" | "empty" => Effect::Pure,
                    // Effect = max of all argument effects.
                    "if" | "progn" | "prog1" | "let" | "let*" | "chain" | "collapse"
                    | "superpose" | "once" => args_effect(),
                    // SpaceRead: reads `k` (QUERY rule in spec) but never mutates it.
                    // RwLock allows concurrent readers → parallelizable.
                    // add-atom/remove-atom classified as SpaceRead because MorkSpace RwLock makes concurrent mutations thread-safe.
                    "match" | "case" | "add-atom" | "remove-atom" => Effect::SpaceRead,
                    // SpaceMutate: forced re-eval or IO.
                    "eval" | "call" | "reduce" | "assert" | "transform-check"
                    | "with_mutex" | "transaction" | "import!"
                    | "foldall" | "map-atom" | "forall" | "within" | "py-call" | "py-eval"
                    | "import-rs!" => Effect::SpaceMutate,
                    _ => {
                        // Registered natives: look up their declared Effect.
                        // Self-recursion: optimistically Pure to avoid infinite loop.
                        let callee_effect = if assume_pure == Some(s.as_str()) {
                            Effect::Pure
                        } else {
                            funcs.effect_of(s, (items.len() - 1) as u8)
                                .unwrap_or(Effect::SpaceMutate) // unknown = conservative
                        };
                        callee_effect.max(args_effect())
                    }
                }
            } else {
                Effect::SpaceMutate // non-symbol head = dynamic dispatch = conservative
            }
        }
    }
}
