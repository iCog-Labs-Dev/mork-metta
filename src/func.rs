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
use std::collections::HashMap;
use std::path::PathBuf;
use crate::parser::Expr;
use crate::atom::Atom;
use crate::space::Space;

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
    pub fn single(atom: Atom) -> Self { NDet::Single(Some(atom)) }
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
#[derive(Clone, Debug)]
pub struct Clause {
    pub patterns: Vec<Expr>,
    pub body: Expr,
}

#[derive(Clone)]
pub enum FunctionKind {
    UserDefined {
        clauses: Vec<Clause>,
    },
    Native {
        // REASON: Arc<dyn Fn + Send + Sync> allows closures captured at startup to be
        // called safely from parallel worker threads.
        func: Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>,
    },
}

/// A named function in the table.
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
    /// Atom storage — wrapped in Mutex so Space impls don't need to be Sync.
    pub space: Mutex<Box<dyn Space + Send>>,
    /// Mutable state store for `get-state`, `change-state!`, `bind!`.
    pub state: Mutex<HashMap<String, Atom>>,
    /// Directory of the file currently being loaded (load-time only).
    pub import_dir: Mutex<PathBuf>,
}

impl Clone for FnTable {
    fn clone(&self) -> Self {
        FnTable {
            map: RwLock::new(self.map.read().unwrap().clone()),
            space: Mutex::new(Box::new(crate::space::ShardedSpace::new_default())),
            state: Mutex::new(HashMap::new()),
            import_dir: Mutex::new(self.import_dir.lock().unwrap().clone()),
        }
    }
}

impl FnTable {
    pub fn new() -> Self {
        FnTable {
            map: RwLock::new(HashMap::new()),
            space: Mutex::new(Box::new(crate::space::ShardedSpace::new_default())),
            state: Mutex::new(HashMap::new()),
            import_dir: Mutex::new(PathBuf::from(".")),
        }
    }

    pub fn with_space(space: Box<dyn Space + Send>) -> Self {
        FnTable {
            map: RwLock::new(HashMap::new()),
            space: Mutex::new(space),
            state: Mutex::new(HashMap::new()),
            import_dir: Mutex::new(PathBuf::from(".")),
        }
    }

    pub fn add_clause(&self, name: String, patterns: Vec<Expr>, body: Expr) {
        let arity = patterns.len() as u8;
        // Infer purity from the body before taking the write lock (the check
        // reads the map). Direct recursion is assumed pure (optimistic);
        // calls to unknown/impure functions make the clause impure.
        let clause_pure =
            crate::eval_parts::data_list::is_pure_expr_assuming(&body, self, &name);
        let clause = Clause { patterns, body };
        let mut map = self.map.write().unwrap();
        let inner = map.entry(name.clone()).or_insert_with(HashMap::new);
        if let Some(arc_func) = inner.get_mut(&arity) {
            // Arc refcount is 1 at load time, so get_mut is zero-copy.
            if let Some(func) = Arc::get_mut(arc_func) {
                if let FunctionKind::UserDefined { ref mut clauses } = func.kind {
                    clauses.push(clause);
                    // A function is pure only if every clause is.
                    func.pure = func.pure && clause_pure;
                    return;
                }
            }
        }
        inner.insert(arity, Arc::new(Function {
            name,
            kind: FunctionKind::UserDefined { clauses: vec![clause] },
            pure: clause_pure,
        }));
    }

    /// Remove a specific clause from a user-defined function.
    /// Returns true if found and removed.
    pub fn remove_clause(&self, name: &str, patterns: &[Expr], body: &Expr) -> bool {
        let arity = patterns.len() as u8;
        let mut map = self.map.write().unwrap();
        let Some(inner) = map.get_mut(name) else { return false; };
        let Some(arc_func) = inner.get_mut(&arity) else { return false; };
        let Some(func) = Arc::get_mut(arc_func) else { return false; };
        if let FunctionKind::UserDefined { ref mut clauses } = func.kind {
            let before = clauses.len();
            clauses.retain(|c| c.patterns.as_slice() != patterns || c.body != *body);
            let removed = clauses.len() < before;
            if clauses.is_empty() {
                inner.remove(&arity);
            }
            return removed;
        }
        false
    }

    pub fn insert_native<F>(&self, name: &str, arity: u8, func: F)
    where
        F: Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static,
    {
        self.map.write().unwrap()
            .entry(name.to_string()).or_insert_with(HashMap::new)
            .insert(arity, Arc::new(Function {
                name: name.to_string(),
                kind: FunctionKind::Native { func: Arc::new(func) },
                pure: false,
            }));
    }

    /// Mark a registered function as pure (no side effects).
    /// Pure functions can have arguments evaluated in parallel.
    /// No-op if the function is not found (e.g. not yet loaded).
    pub fn mark_pure(&self, name: &str, arity: u8) {
        if let Some(arc_func) = self.map.write().unwrap()
            .get_mut(name).and_then(|inner| inner.get_mut(&arity))
            .and_then(|a| Arc::get_mut(a))
        {
            arc_func.pure = true;
        }
    }

    /// Check existence — zero allocation.
    pub fn has(&self, name: &str, arity: u8) -> bool {
        self.map.read().unwrap()
            .get(name).map_or(false, |inner| inner.contains_key(&arity))
    }

    /// Return the `Arc<Function>` for a named function at the given arity.
    /// The Arc clone is O(1).
    pub fn get(&self, name: &str, arity: u8) -> Option<Arc<Function>> {
        self.map.read().unwrap()
            .get(name).and_then(|inner| inner.get(&arity)).cloned()
    }

    /// Check if a named function is pure at the given arity.
    /// Returns `false` if the function is not found (conservative).
    pub fn is_pure(&self, name: &str, arity: u8) -> bool {
        self.map.read().unwrap()
            .get(name).and_then(|inner| inner.get(&arity))
            .map(|f| f.pure)
            .unwrap_or(false)
    }
}
