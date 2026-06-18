use crate::env::Env;
use crate::parser::Expr;
use dashu::Integer as IBig;
use dashu::Decimal as DBig;

/// A growing numeric value — either an arbitrary-precision integer or decimal.
/// Integer values up to ~2×64 bits are stored inline (no heap alloc); larger
/// values promote to heap. Decimal values are exact (no NaN, no IEEE rounding).
#[derive(Clone, Debug)]
pub enum Numeric {
    /// Arbitrary-precision signed integer.
    Int(IBig),
    /// Arbitrary-precision signed decimal (exact, no NaN/Inf).
    Dec(DBig),
}

impl PartialEq for Numeric {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Numeric::Int(a), Numeric::Int(b)) => a == b,
            (Numeric::Dec(a), Numeric::Dec(b)) => a == b,
            _ => false, // Int and Dec are distinct types
        }
    }
}
impl Eq for Numeric {}

impl std::fmt::Display for Numeric {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Numeric::Int(n) => write!(f, "{}", n),
            Numeric::Dec(d) => write!(f, "{}", d),
        }
    }
}

impl Numeric {
    /// True if the value is zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Numeric::Int(n) => *n == IBig::from(0i32),
            Numeric::Dec(d) => *d == DBig::from(0i32),
        }
    }
}

/// Core value type for the MeTTa evaluator.
///
/// Every value in MeTTa is an Atom. Atoms are either:
/// - `Num(Numeric)` — arbitrary-precision integers and decimals (no overflow, no NaN)
/// - `Sym(String)` — symbolic names (functions, variables, bare symbols)
/// - `Str(String)` — string literals (distinct from symbols, e.g. `"hello"` vs `hello`)
/// - `Expr(Vec<Atom>)` — S-expressions (nested lists)
/// - `Closure { params, body, env }` — anonymous functions (|->)
///
/// Variables like `$N` are represented as `Sym("$N")` at the parsing stage and
/// are replaced by their values from the environment during evaluation.
///
/// # Assumptions
/// - Numbers are arbitrary-precision integers or decimals via `dashu`.
/// - Symbols are Unicode strings stored as `Arc<str>` (shared, O(1) clone).
/// - Strings are Unicode strings stored as `Arc<str>`, distinct from symbols.
/// - `Expr` is an owned, fully-evaluated value — not a thunk or promise.
/// - `Atom::Expr` with no elements represents the empty list `()`.
/// - Equality is structural (recursive). Str != Sym even with same content.
/// - Empty symbol `Sym("")` represents MeTTa's `Empty` / false / unit value.
/// - `Closure` equality compares params, body, and captured env structurally.
use std::sync::Arc;

/// Heap-allocated closure fields — boxed so `Atom` stays 32 bytes.
#[derive(Clone, Debug, PartialEq)]
pub struct ClosureData {
    pub params: Vec<Expr>,
    pub body: Expr,
    pub env: Env,
}

#[derive(Clone, Debug)]
pub enum Atom {
    /// A symbolic name: function names, variable names (with $ prefix), data symbols.
    /// Stored as Arc<str> so cloning is O(1) — hot paths clone symbols frequently.
    Sym(Arc<str>),
    /// A string literal value, distinct from symbols.
    /// `"hello"` in source → `Str("hello")`, NOT equal to symbol `hello`.
    Str(Arc<str>),
    /// An arbitrary-precision integer or decimal.
    Num(Numeric),
    /// An S-expression — ordered list of atoms. Arc-shared so clone is O(1).
    Expr(Arc<[Atom]>),
    /// An anonymous function created by `|->`. Boxed to keep Atom at 32 bytes.
    Closure(Box<ClosureData>),
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Atom::Sym(a), Atom::Sym(b)) => a == b,
            (Atom::Str(a), Atom::Str(b)) => a == b,
            (Atom::Num(a), Atom::Num(b)) => a == b, // delegates to Numeric::PartialEq
            (Atom::Expr(a), Atom::Expr(b)) => Arc::ptr_eq(a, b) || a == b,
            (Atom::Closure(a), Atom::Closure(b)) => a == b,
            _ => false,
        }
    }
}
impl Eq for Atom {}

impl std::hash::Hash for Atom {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Atom::Sym(s) => s.hash(state),
            Atom::Str(s) => s.hash(state),
            Atom::Num(n) => n.to_string().hash(state),
            Atom::Expr(items) => {
                items.len().hash(state);
                for a in items.iter() {
                    a.hash(state);
                }
            }
            Atom::Closure(c) => c.body.to_string().hash(state),
        }
    }
}

impl Atom {
    /// Format an Atom as an S-expression string (for display and repr).
    ///
    /// # Assumptions
    /// - The result is valid MeTTa (can be re-parsed by a compliant reader).
    pub fn to_sexpr_string(&self) -> String {
        match self {
            Atom::Sym(s) => s.to_string(),
            Atom::Str(s) => {
                let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
                format!("\"{}\"", escaped)
            }
            Atom::Num(n) => n.to_string(), // uses Numeric::Display
            Atom::Expr(items) => {
                let inner: Vec<String> = items.iter().map(|a| a.to_sexpr_string()).collect();
                format!("({})", inner.join(" "))
            }
            Atom::Closure(c) => {
                let param_strs: Vec<String> = c.params.iter().map(|p| p.to_string()).collect();
                format!("(|-> ({}) {})", param_strs.join(" "), c.body.to_string())
            }
        }
    }

    /// Convenience: create a symbol atom.
    /// Normalizes boolean literals to canonical lowercase (PeTTa convention).
    pub fn sym(s: &str) -> Self {
        let canonical = match s {
            "True" => "true",
            "False" => "false",
            other => other,
        };
        Atom::Sym(Arc::from(canonical))
    }

    /// Convenience: create a string atom.
    pub fn str_val(s: &str) -> Self {
        Atom::Str(Arc::from(s))
    }

    /// Convenience: create a number atom.
    /// Construct an integer atom from an i128 (the common small-integer fast path).
    pub fn num(n: i128) -> Self {
        Atom::Num(Numeric::Int(IBig::from(n)))
    }

    /// Construct a decimal atom by parsing a string (e.g. "3.14").
    pub fn decimal(s: &str) -> Result<Self, String> {
        s.parse::<DBig>()
            .map(|d| Atom::Num(Numeric::Dec(d)))
            .map_err(|e| format!("invalid decimal '{}': {}", s, e))
    }

    /// Convenience: create an expression atom.
    pub fn expr(items: Vec<Atom>) -> Self {
        Atom::Expr(Arc::from(items))
    }

    /// Extract the integer value as i128. Fails if the number is a decimal or
    /// too large for i128.
    ///
    /// # Errors
    /// Returns an error description if the atom is not a number.
    pub fn as_num(&self) -> Result<i128, String> {
        match self {
            Atom::Num(Numeric::Int(n)) => {
                i128::try_from(n.clone()).map_err(|_| format!("integer {} overflows i128", n))
            }
            Atom::Num(Numeric::Dec(d)) => {
                Err(format!("expected integer, got decimal {}", d))
            }
            other => Err(format!("expected number, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the Numeric value from a Num atom.
    pub fn as_numeric(&self) -> Result<&Numeric, String> {
        match self {
            Atom::Num(n) => Ok(n),
            other => Err(format!("expected number, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the symbol string from a `Sym` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not a symbol.
    pub fn as_sym(&self) -> Result<&str, String> {
        match self {
            Atom::Sym(s) => Ok(s.as_ref()),
            other => Err(format!("expected symbol, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the string content from a `Str` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not a string.
    pub fn as_str_val(&self) -> Result<&str, String> {
        match self {
            Atom::Str(s) => Ok(s.as_ref()),
            other => Err(format!("expected string, got {}", other.to_sexpr_string())),
        }
    }

    /// Extract the element slice from an `Expr` variant.
    ///
    /// # Errors
    /// Returns an error description if the atom is not an expression.
    pub fn as_expr(&self) -> Result<&[Atom], String> {
        match self {
            Atom::Expr(items) => Ok(items.as_ref()),
            other => Err(format!(
                "expected expression, got {}",
                other.to_sexpr_string()
            )),
        }
    }

    /// MeTTa truthiness: `Num(0)` and empty `Sym("")` are false; all else is true.
    ///
    /// # Assumptions
    /// - `Expr` with any elements is always truthy (PeTTa convention).
    /// - Empty expression `Expr([])` is truthy (non-zero structure).
    /// - `Closure` is always truthy.
    /// - Strings are always truthy.
    pub fn is_truthy(&self) -> bool {
        match self {
            Atom::Num(n) if n.is_zero() => false,
            Atom::Sym(s) if s.is_empty() || s.as_ref().eq_ignore_ascii_case("false") => false,
            _ => true,
        }
    }
}
