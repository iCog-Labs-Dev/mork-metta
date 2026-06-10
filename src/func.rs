/// Function dispatch table.
///
/// Stores both user-defined functions (compiled from `(= ...)` forms) and
/// native (grounded) Rust functions.
///
/// # Assumptions
/// - User-defined functions have a fixed param list (no varargs, no optional args).
/// - Native functions receive fully-evaluated argument atoms and return an NDet
///   iterator (possibly with one element for deterministic functions).
/// - The FnTable is the sole dispatch mechanism — no dynamic dispatch or
///   multi-method infrastructure.

use std::collections::HashMap;
use crate::parser::Expr;
use crate::atom::Atom;
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
///
/// Each `Clause` corresponds to one `(= (name patterns...) body)` form.
/// Patterns support: `$var` (bind), literal symbols/numbers (exact match),
/// and nested lists (structural match).
#[derive(Clone, Debug)]
pub struct Clause {
    /// Pattern expressions for each argument (supports $var, literals, nested lists).
    pub patterns: Vec<Expr>,
    /// Body expression to evaluate when this clause matches.
    pub body: Expr,
}
#[derive(Clone)]
pub enum FunctionKind {
    /// Compiled from one or more MeTTa `(= ...)` definitions.
    /// Multiple clauses with the same name produce a nondeterministic stream:
    /// each matching clause contributes its results.
    UserDefined {
        /// All clauses for this function, tried in definition order.
        clauses: Vec<Clause>,
    },
    /// A Rust native function.
    Native {
        // REASON: The fn pointer type is unavoidably complex —
        // it takes atom slices + fn table ref, returns Result<NDet, String>.
        // There is no simpler way to express this signature.
        #[allow(clippy::type_complexity)]
        func: fn(&[Atom], &FnTable) -> Result<NDet, String>,
    },
}
/// A named function in the table.
#[derive(Clone)]
pub struct Function {
    pub name: String,
    pub kind: FunctionKind,
}

/// The function dispatch table.
#[derive(Clone)]
pub struct FnTable {
    map: HashMap<(String, u8), Function>,
}
impl FnTable {
    pub fn new() -> Self {
        FnTable {
            map: HashMap::new(),
        }
    }
    /// Add a clause to a user-defined function.
    ///
    /// Arity is computed from `patterns.len()` — functions with different
    /// arities are stored as separate entries, avoiding wrong-arity iteration.
    ///
    /// If the function already exists at this arity, the clause is appended
    /// (creating multi-clause dispatch). If not, a new entry is created.
    ///
    /// # Assumptions
    /// - Native functions cannot have clauses appended.
    /// - Clauses are tried in definition order on dispatch.
    pub fn add_clause(&mut self, name: String, patterns: Vec<Expr>, body: Expr) {
        // SAFETY: patterns.len() is the arity of a parsed function head.
        // No MeTTa function has >255 parameters — the parser/stack would
        // overflow long before that. The cast to u8 is safe.
        let arity = patterns.len() as u8;
        let clause = Clause { patterns, body };
        if let Some(func) = self.map.get_mut(&(name.clone(), arity)) {
            if let FunctionKind::UserDefined { ref mut clauses } = func.kind {
                clauses.push(clause);
                return;
            }
        }
        // New function entry at this arity
        self.map.insert((name.clone(), arity), Function {
            name,
            kind: FunctionKind::UserDefined {
                clauses: vec![clause],
            },
        });
    }
    /// Insert a native function with a fixed arity.
    ///
    /// The arity is used for dispatch: only calls with exactly `arity`
    /// arguments will match this entry. This prevents wrong-arity calls
    /// from silently dispatching.
    ///
    /// # Assumptions
    /// - Native functions have a single, fixed arity (no overloading).
    pub fn insert_native(
        &mut self,
        name: &str,
        arity: u8,
        func: fn(&[Atom], &FnTable) -> Result<NDet, String>,
    ) {
        self.map.insert(
            (name.to_string(), arity),
            Function {
                name: name.to_string(),
                kind: FunctionKind::Native { func },
            },
        );
    }
    /// Look up a function by name and arity.
    ///
    /// Returns `None` if no function is registered under that exact
    /// name+arity combination.
    pub fn get(&self, name: &str, arity: u8) -> Option<&Function> {
        self.map.get(&(name.to_string(), arity))
    }
}
