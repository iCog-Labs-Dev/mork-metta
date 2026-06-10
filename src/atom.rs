/// Core value type for the MeTTa evaluator.
///
/// Every value in MeTTa is an Atom. Atoms are either:
/// - `Num(i64)` — integer numbers
/// - `Sym(String)` — symbolic names (functions, variables, bare symbols)
/// - `Expr(Vec<Atom>)` — S-expressions (nested lists)
/// - `Closure { params, body, env }` — anonymous functions (|->)
///
/// Variables like `$N` are represented as `Sym("$N")` at the parsing stage and
/// are replaced by their values from the environment during evaluation.
///
/// # Assumptions
/// - Numbers are 64-bit signed integers (no floats, no bigints).
/// - Symbols are Unicode strings stored as-is (no interning).
/// - `Expr` is an owned, fully-evaluated value — not a thunk or promise.
/// - `Atom::Expr` with no elements represents the empty list `()`.
/// - Equality is structural (recursive).
/// - Empty symbol `Sym("")` represents MeTTa's `Empty` / false / unit value.
/// - `Closure` equality compares params, body, and captured env structurally.
use crate::env::Env;
use crate::parser::Expr;

#[derive(Clone, Debug)]
pub enum Atom {
    /// A symbolic name: function names, variable names (with $ prefix), data symbols.
    Sym(String),
    /// A 64-bit signed integer.
    Num(i64),
    /// An S-expression — ordered list of atoms.
    Expr(Vec<Atom>),
    /// An anonymous function created by `|->`.
    Closure {
        /// Parameter patterns (e.g. `[$x, $y]`).
        params: Vec<Expr>,
        /// Body expression.
        body: Box<Expr>,
        /// Captured lexical environment at definition site.
        env: Box<Env>,
    },
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Atom::Sym(a), Atom::Sym(b)) => a == b,
            (Atom::Num(a), Atom::Num(b)) => a == b,
            (Atom::Expr(a), Atom::Expr(b)) => a == b,
            (
                Atom::Closure { params: p1, body: b1, env: e1 },
                Atom::Closure { params: p2, body: b2, env: e2 },
            ) => p1 == p2 && b1 == b2 && e1 == e2,
            _ => false,
        }
    }
}

impl Atom {
    /// Format an Atom as an S-expression string (for display).
    ///
    /// # Assumptions
    /// - The result is valid MeTTa (can be re-parsed by a compliant reader).
    pub fn to_sexpr_string(&self) -> String {
        match self {
            Atom::Sym(s) => s.clone(),
            Atom::Num(n) => n.to_string(),
            Atom::Expr(items) => {
                let inner: Vec<String> = items.iter().map(|a| a.to_sexpr_string()).collect();
                format!("({})", inner.join(" "))
            }
            Atom::Closure { params, body, .. } => {
                let param_strs: Vec<String> = params.iter().map(|p| p.to_string()).collect();
                format!("(|-> ({}) {})", param_strs.join(" "), body.to_string())
            }
        }
    }

    /// Convenience: create a symbol atom.
    pub fn sym(s: &str) -> Self {
        Atom::Sym(s.to_string())
    }

    /// Convenience: create a number atom.
    pub fn num(n: i64) -> Self {
        Atom::Num(n)
    }

    /// Convenience: create an expression atom.
    pub fn expr(items: Vec<Atom>) -> Self {
        Atom::Expr(items)
    }

    /// Extract the numeric value from a `Num` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not a number.
    pub fn as_num(&self) -> Result<i64, String> {
        match self {
            Atom::Num(n) => Ok(*n),
            other => Err(format!("expected number, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the symbol string from a `Sym` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not a symbol.
    pub fn as_sym(&self) -> Result<&str, String> {
        match self {
            Atom::Sym(s) => Ok(s.as_str()),
            other => Err(format!("expected symbol, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the element slice from an `Expr` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not an expression.
    pub fn as_expr(&self) -> Result<&[Atom], String> {
        match self {
            Atom::Expr(items) => Ok(items.as_slice()),
            other => Err(format!("expected expression, got {}", other.to_sexpr_string())),
        }
    }

    /// MeTTa truthiness: `Num(0)` and empty `Sym("")` are false; all else is true.
    ///
    /// # Assumptions
    /// - `Expr` with any elements is always truthy (PeTTa convention).
    /// - Empty expression `Expr([])` is truthy (non-zero structure).
    /// - `Closure` is always truthy.
    pub fn is_truthy(&self) -> bool {
        match self {
            Atom::Num(0) => false,
            Atom::Sym(s) if s.is_empty() => false,
            _ => true,
        }
    }
}
