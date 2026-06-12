/// Function dispatch table.
///
/// Stores both user-defined functions (compiled from `(= ...)` forms) and
/// native (grounded) Rust functions. Also owns the atom space reference and
/// mutable state store for space/state operations.
///
/// # Assumptions
/// - User-defined functions have a fixed param list (no varargs, no optional args).
/// - Native functions receive fully-evaluated argument atoms and return an NDet
///   iterator (possibly with one element for deterministic functions).
/// - The FnTable is the sole dispatch mechanism — no dynamic dispatch or
///   multi-method infrastructure.
/// - Space + state are stored behind `RefCell` for interior mutability — both
///   builtins and special forms can access them through `&FnTable`.

use std::cell::{Ref, RefCell};
use std::sync::Arc;
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
///
/// # Assumptions
/// - `NDet` is lazy: results are produced on demand.
/// - `NDet` can be empty (no results) for failed matches or unsatisfiable forms.
/// - `Single(atom)` yields one atom then stops.
/// - `Stream(iter)` delegates to the inner iterator.
pub enum NDet {
    /// A single result (common case — no heap allocation).
    Single(Option<Atom>),
    /// Multiple or lazy results (heap-allocated iterator).
    Stream(Box<dyn Iterator<Item = Atom>>),
}
impl NDet {
    /// Create an `NDet` that yields exactly one atom (zero heap alloc).
    pub fn single(atom: Atom) -> Self {
        NDet::Single(Some(atom))
    }
    /// Create an `NDet` from an iterator of atoms.
    pub fn stream(iter: impl Iterator<Item = Atom> + 'static) -> Self {
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
        // REASON: Arc<dyn Fn> allows closures that capture context (e.g. loaded plugin fns).
        func: Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + 'static>,
    },
}
/// A named function in the table.
#[derive(Clone)]
pub struct Function {
    pub name: String,
    pub kind: FunctionKind,
}

/// The function dispatch table — also owns the atom space + mutable state.
/// Two-level map: name → (arity → Function).
/// Outer lookup uses `HashMap::get(&str)` via Borrow<str> — zero allocation.
type FuncMap = HashMap<String, HashMap<u8, Function>>;

pub struct FnTable {
    map: RefCell<FuncMap>,
    /// Atom storage space for `add-atom`, `remove-atom`, `match`.
    pub space: RefCell<Box<dyn Space>>,
    /// Mutable state store for `get-state`, `change-state!`, `bind!`.
    pub state: RefCell<HashMap<String, Atom>>,
    /// Directory of the file currently being loaded.
    /// Updated before each file load and restored after — forms a stack
    /// across nested imports so relative paths always resolve correctly.
    pub import_dir: RefCell<PathBuf>,
}

impl Clone for FnTable {
    fn clone(&self) -> Self {
        FnTable {
            map: RefCell::new(self.map.borrow().clone()),
            space: RefCell::new(crate::space::LocalSpace::new_box()),
            state: RefCell::new(HashMap::new()),
            import_dir: RefCell::new(self.import_dir.borrow().clone()),
        }
    }
}

impl FnTable {
    pub fn new() -> Self {
        FnTable {
            map: RefCell::new(HashMap::new()),
            space: RefCell::new(crate::space::LocalSpace::new_box()),
            state: RefCell::new(HashMap::new()),
            import_dir: RefCell::new(PathBuf::from(".")),
        }
    }

    pub fn with_space(space: Box<dyn Space>) -> Self {
        FnTable {
            map: RefCell::new(HashMap::new()),
            space: RefCell::new(space),
            state: RefCell::new(HashMap::new()),
            import_dir: RefCell::new(PathBuf::from(".")),
        }
    }

    pub fn add_clause(&self, name: String, patterns: Vec<Expr>, body: Expr) {
        // SAFETY: no MeTTa function has >255 parameters in practice.
        let arity = patterns.len() as u8;
        let clause = Clause { patterns, body };
        let mut map = self.map.borrow_mut();
        let inner = map.entry(name.clone()).or_insert_with(HashMap::new);
        if let Some(func) = inner.get_mut(&arity) {
            if let FunctionKind::UserDefined { ref mut clauses } = func.kind {
                clauses.push(clause);
                return;
            }
        }
        inner.insert(arity, Function {
            name,
            kind: FunctionKind::UserDefined { clauses: vec![clause] },
        });
    }

    /// Remove a specific clause from a user-defined function.
    /// If no clauses remain after removal, the function entry is dropped entirely.
    /// Returns true if a matching clause was found and removed.
    pub fn remove_clause(&self, name: &str, patterns: &[Expr], body: &Expr) -> bool {
        // SAFETY: patterns.len() < 256 in all MeTTa programs.
        let arity = patterns.len() as u8;
        let mut map = self.map.borrow_mut();
        let Some(inner) = map.get_mut(name) else { return false; };
        let Some(func) = inner.get_mut(&arity) else { return false; };
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

    pub fn insert_native<F>(
        &self,
        name: &str,
        arity: u8,
        func: F,
    ) where
        F: Fn(&[Atom], &FnTable) -> Result<NDet, String> + 'static,
    {
        self.map.borrow_mut()
            .entry(name.to_string()).or_insert_with(HashMap::new)
            .insert(arity, Function {
                name: name.to_string(),
                kind: FunctionKind::Native { func: Arc::new(func) },
            });
    }

    /// Returns a borrowed reference — zero String allocation, no Function clone.
    /// Uses Borrow<str> on the outer map so `name` lookup needs no to_string().
    pub fn get_ref(&self, name: &str, arity: u8) -> Option<Ref<'_, Function>> {
        Ref::filter_map(self.map.borrow(), |m| {
            m.get(name).and_then(|inner| inner.get(&arity))
        }).ok()
    }

    /// Check existence — zero allocation via Borrow<str>.
    pub fn has(&self, name: &str, arity: u8) -> bool {
        self.map.borrow().get(name).map_or(false, |inner| inner.contains_key(&arity))
    }

    pub fn get(&self, name: &str, arity: u8) -> Option<Function> {
        self.map.borrow().get(name).and_then(|inner| inner.get(&arity)).cloned()
    }
}
