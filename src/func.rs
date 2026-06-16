use crate::atom::Atom;
use crate::parser::Expr;
use crate::space::Space;
use std::collections::HashMap;
use std::path::PathBuf;
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
    pub pure: bool,
}

/// Two-level function map: name → (arity → Function).
type FuncMap = HashMap<String, HashMap<u8, Arc<Function>>>;

pub struct FnTable {
    /// Read-heavy: many concurrent lookups during eval, writes only at load time.
    map: RwLock<FuncMap>,
    /// Atom storage — RwLock allows concurrent readers (queries), exclusive writers (add/remove).
    pub space: RwLock<Box<dyn Space + Send + Sync>>,
    /// Lazily-created named spaces addressed by `&name`.
    pub named_spaces: Mutex<HashMap<String, Box<dyn Space + Send + Sync>>>,
    /// Mutable state store for `get-state`, `change-state!`, `bind!`.
    pub state: Mutex<HashMap<String, Atom>>,
    /// Function definition cache — populated from space at reify time, updated
    /// on add-atom/remove-atom. Read-heavy (every function dispatch), so RwLock.
    pub fn_cache: RwLock<HashMap<String, HashMap<u8, Vec<Clause>>>>,
    /// Space-free purity of each user function, computed at definition time and
    /// recomputed on redefinition (self-evolution-stable). Drives the *only*
    /// sound parallelization decision: a function is parallel-safe iff it (and
    /// everything it calls) performs no space access and no IO. Absent ⇒ impure.
    pub fn_purity: RwLock<HashMap<String, HashMap<u8, bool>>>,
    /// Directory of the file currently being loaded (load-time only).
    pub import_dir: Mutex<PathBuf>,
}

impl FnTable {
    pub fn new() -> Self {
        FnTable {
            map: RwLock::new(HashMap::new()),
            space: RwLock::new(Box::new(crate::space::MorkSpace::new())),
            named_spaces: Mutex::new(HashMap::new()),
            fn_cache: RwLock::new(HashMap::new()),
            fn_purity: RwLock::new(HashMap::new()),
            state: Mutex::new(HashMap::new()),
            import_dir: Mutex::new(PathBuf::from(".")),
        }
    }

    pub fn with_space(space: Box<dyn Space + Send>) -> Self {
        FnTable {
            map: RwLock::new(HashMap::new()),
            space: RwLock::new(space),
            named_spaces: Mutex::new(HashMap::new()),
            fn_cache: RwLock::new(HashMap::new()),
            fn_purity: RwLock::new(HashMap::new()),
            state: Mutex::new(HashMap::new()),
            import_dir: Mutex::new(PathBuf::from(".")),
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
            .or_insert_with(HashMap::new)
            .insert(
                arity,
                Arc::new(Function {
                    name: name.to_string(),
                    kind: FunctionKind::Native {
                        func: Arc::new(func),
                    },
                    pure: false,
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
            arc_func.pure = true;
        }
    }

    pub fn has(&self, name: &str, arity: u8) -> bool {
        self.map
            .read()
            .unwrap()
            .get(name)
            .map_or(false, |inner| inner.contains_key(&arity))
    }

    pub fn get(&self, name: &str, arity: u8) -> Option<Arc<Function>> {
        self.map
            .read()
            .unwrap()
            .get(name)
            .and_then(|inner| inner.get(&arity))
            .cloned()
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
                let mut spaces = self.named_spaces.lock().unwrap();
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

    pub fn cache_fn(&self, name: &str, arity: u8, clause: Clause) {
        // Compute space-free purity BEFORE taking the cache write lock: the
        // analysis reads fn_cache/fn_purity, so locking first would deadlock.
        // Self-recursion is optimistically pure, so directly recursive pure
        // functions (e.g. fib) stay parallelizable.
        let clause_pure =
            is_pure_expr_assuming(&clause.body, self, name);

        {
            let mut cache = self.fn_cache.write().unwrap();
            let clauses = cache
                .entry(name.to_string())
                .or_insert_with(HashMap::new)
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

        // A function is parallel-safe only if EVERY clause is pure.
        let mut purity = self.fn_purity.write().unwrap();
        let entry = purity
            .entry(name.to_string())
            .or_insert_with(HashMap::new)
            .entry(arity)
            .or_insert(true);
        *entry = *entry && clause_pure;
    }

    pub fn uncache_fn(&self, name: &str, arity: u8) {
        if let Some(inner) = self.fn_cache.write().unwrap().get_mut(name) {
            inner.remove(&arity);
        }
        if let Some(inner) = self.fn_purity.write().unwrap().get_mut(name) {
            inner.remove(&arity);
        }
    }

    /// Check if a named function is pure at the given arity.
    /// Returns `false` if the function is not found (conservative).
    pub fn is_pure(&self, name: &str, arity: u8) -> bool {
        // Native builtins carry an authoritative space-free purity flag.
        if let Some(inner) = self.map.read().unwrap().get(name) {
            if let Some(f) = inner.get(&arity) {
                return f.pure;
            }
        }
        // User-defined functions: purity computed at definition time (sound and
        // self-evolution-stable). Unknown symbols and defs added directly to the
        // space are treated as impure — never parallelized on an unproven
        // assumption. (A cache miss still dispatches correctly via the space
        // fallback; it just runs sequentially.)
        self.fn_purity
            .read()
            .unwrap()
            .get(name)
            .and_then(|inner| inner.get(&arity))
            .copied()
            .unwrap_or(false)
    }
}

fn is_pure_expr_assuming(expr: &crate::parser::Expr, funcs: &FnTable, self_name: &str) -> bool {
    is_pure_expr_inner(expr, funcs, Some(self_name))
}

fn is_pure_expr_inner(
    expr: &crate::parser::Expr,
    funcs: &FnTable,
    assume_pure: Option<&str>,
) -> bool {
    use crate::parser::Expr;
    match expr {
        Expr::Number(_) | Expr::Symbol(_) => true,
        Expr::List(items) if items.is_empty() => true,
        Expr::List(items) => {
            let args_pure =
                || items[1..].iter().all(|e| is_pure_expr_inner(e, funcs, assume_pure));
            if let Expr::Symbol(s) = &items[0] {
                match s.as_str() {
                    "quote" | "superpose" | "empty" | "repr" | "|->" | "once" => true,
                    "if" | "progn" | "let" | "let*" | "chain" | "collapse" => args_pure(),
                    "eval" | "call" | "reduce" | "assert" | "transform" | "add-atom"
                    | "remove-atom" | "match" | "with_mutex" | "transaction" | "import!"
                    | "readln!" | "println!" | "case" | "foldall" | "map-atom" | "forall"
                    | "within" | "py-call" | "import-rs!" => false,
                    _ => {
                        let callee_pure = assume_pure == Some(s.as_str())
                            || funcs.is_pure(s, (items.len() - 1) as u8);
                        callee_pure && args_pure()
                    }
                }
            } else {
                false
            }
        }
    }
}
