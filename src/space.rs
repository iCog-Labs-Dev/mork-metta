/// Atom storage backends for the MeTTa evaluator.
///
/// The `Space` trait is the core abstraction: a store of S-expression atoms
/// that supports add, remove, match, and enumeration.
///
/// Two implementations:
/// - `LocalSpace` — simple `Vec`-based storage (no dependencies)
/// - `MorkSpace` — wraps MORK's `PathMap` trie (requires `mork` feature)

use std::collections::HashMap;
use crate::atom::Atom;
use crate::parser::Expr;

/// A pattern for matching against atoms in a space.
///
/// Supports:
/// - `Any`       — anonymous wildcard, matches anything, no binding
/// - `Var(name)` — named wildcard ($x), matches anything, binds name → atom
/// - `Exact(a)`  — must match atom `a` exactly
/// - `Expr(pats)`— matches an `Atom::Expr` structurally
///
/// Stored atoms that contain `$var` symbols are treated as Prolog-style
/// unification variables: they match any query pattern and are substituted
/// with the matched value throughout the returned atom.
#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(String),
    Exact(Atom),
    Expr(Vec<Pattern>),
}

impl Pattern {
    /// Construct a pattern from a parsed Expr tree.
    /// `$`-prefixed symbols become `Var(name)`; others become `Exact`.
    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Symbol(s) if s.starts_with('$') => Pattern::Var(s.clone()),
            Expr::Symbol(s) => Pattern::Exact(Atom::Sym(s.clone())),
            Expr::Number(n) => Pattern::Exact(Atom::Num(*n)),
            Expr::List(items) => {
                Pattern::Expr(items.iter().map(Self::from_expr).collect())
            }
        }
    }
}

/// A match result: the matched atom (stored vars substituted) plus query bindings.
#[derive(Clone, Debug)]
pub struct MatchResult {
    /// The matched atom with any stored `$var` symbols replaced by their matched values.
    pub atom: Atom,
    /// Bindings for query `$var` patterns: name → matched (and substituted) atom.
    pub bindings: Vec<(String, Atom)>,
}

/// Space trait: abstract atom storage backend.
pub trait Space {
    /// Add an atom to the space.
    fn add_atom(&mut self, atom: &Atom) -> Result<(), String>;

    /// Remove an atom from the space. Returns true if something was removed.
    fn remove_atom(&mut self, atom: &Atom) -> Result<bool, String>;

    /// Match atoms against a pattern. Returns all matching atoms and bindings.
    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult>;

    /// Return all atoms in the space.
    fn get_atoms(&self) -> Vec<Atom>;

    /// Return a human-readable description of the backend.
    fn description(&self) -> &str;
}

// ========================================================================
// LocalSpace — HashMap-indexed storage, no dependencies
// ========================================================================

/// Extract the index key `(functor, list_len)` for an atom, if it has one.
/// Only `Atom::Expr` starting with a `Sym` is indexable.
fn index_key(atom: &Atom) -> Option<(String, usize)> {
    if let Atom::Expr(items) = atom {
        if let Some(Atom::Sym(f)) = items.first() {
            return Some((f.clone(), items.len()));
        }
    }
    None
}

/// Extract the index key a pattern can use for O(1) candidate lookup.
/// Returns `None` when the first position is a wildcard/variable — full scan required.
fn pattern_index_key(pattern: &Pattern) -> Option<(String, usize)> {
    match pattern {
        Pattern::Expr(pats) => match pats.first()? {
            Pattern::Exact(Atom::Sym(f)) => Some((f.clone(), pats.len())),
            _ => None,
        },
        Pattern::Exact(Atom::Expr(items)) => match items.first()? {
            Atom::Sym(f) => Some((f.clone(), items.len())),
            _ => None,
        },
        _ => None,
    }
}

/// In-memory space indexed by `(functor, list_length)` for O(1) candidate lookup.
///
/// `(foo arg1 arg2)` atoms are stored in a bucket keyed by `("foo", 3)`.
/// A pattern `(foo $x $y)` resolves to that bucket directly instead of scanning
/// the entire space — matching k candidates instead of n total atoms.
/// Bare `Sym`, `Num`, and non-symbol-headed `Expr` atoms fall into a scalar fallback.
#[derive(Clone, Default)]
pub struct LocalSpace {
    indexed: HashMap<(String, usize), Vec<Atom>>,
    scalars: Vec<Atom>,
}

impl LocalSpace {
    pub fn new() -> Self { Self::default() }
    pub fn new_box() -> Box<dyn Space> { Box::new(Self::default()) }
}

impl Space for LocalSpace {
    fn add_atom(&mut self, atom: &Atom) -> Result<(), String> {
        if let Some(key) = index_key(atom) {
            self.indexed.entry(key).or_default().push(atom.clone());
        } else {
            self.scalars.push(atom.clone());
        }
        Ok(())
    }

    fn remove_atom(&mut self, atom: &Atom) -> Result<bool, String> {
        if let Some(key) = index_key(atom) {
            if let Some(vec) = self.indexed.get_mut(&key) {
                let before = vec.len();
                vec.retain(|a| a != atom);
                let removed = vec.len() < before;
                if vec.is_empty() { self.indexed.remove(&key); }
                return Ok(removed);
            }
            return Ok(false);
        }
        let before = self.scalars.len();
        self.scalars.retain(|a| a != atom);
        Ok(self.scalars.len() < before)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        if let Some(key) = pattern_index_key(pattern) {
            // Hot path: only unify against atoms in the matching bucket.
            return self.indexed.get(&key)
                .map(|atoms| atoms.iter().filter_map(|a| match_one(pattern, a)).collect())
                .unwrap_or_default();
        }
        // Full scan: wildcard or variable at functor position.
        self.indexed.values()
            .flat_map(|v| v.iter())
            .chain(self.scalars.iter())
            .filter_map(|a| match_one(pattern, a))
            .collect()
    }

    fn get_atoms(&self) -> Vec<Atom> {
        self.indexed.values()
            .flat_map(|v| v.iter().cloned())
            .chain(self.scalars.iter().cloned())
            .collect()
    }

    fn description(&self) -> &str { "LocalSpace (indexed by functor+arity)" }
}

// ========================================================================
// MorkSpace — wraps MORK's PathMap trie
// ========================================================================

/// Space backed by MORK's hypergraph trie, with a shadow `LocalSpace` for queries.
///
/// Writes go to the kernel PathMap (byte-encoded S-expressions) for persistence.
/// Reads are served from the shadow — zero serialization round-trip, and first-
/// argument indexing via `LocalSpace`'s HashMap buckets. The previous design
/// called `dump_all_sexpr()` on every query, re-parsing the entire space each time.
#[cfg(feature = "mork")]
pub struct MorkSpace {
    inner: mork::space::Space<mork::weightedsweep::U64AtomHeader>,
    /// Mirrors `inner` in Rust form — serves all read operations without going
    /// through the serialization round-trip.
    shadow: LocalSpace,
}

#[cfg(feature = "mork")]
impl MorkSpace {
    pub fn new() -> Self {
        MorkSpace {
            inner: mork::space::Space::new(),
            shadow: LocalSpace::new(),
        }
    }
}

#[cfg(feature = "mork")]
impl Space for MorkSpace {
    fn add_atom(&mut self, atom: &Atom) -> Result<(), String> {
        let sexpr = atom.to_sexpr_string();
        self.inner.add_all_sexpr(sexpr.as_bytes())?;
        self.shadow.add_atom(atom)
    }

    fn remove_atom(&mut self, atom: &Atom) -> Result<bool, String> {
        let sexpr = atom.to_sexpr_string();
        let count = self.inner.remove_all_sexpr(sexpr.as_bytes())?;
        self.shadow.remove_atom(atom)?;
        Ok(count > 0)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        // Shadow: no dump_all_sexpr, no parse loop, first-arg indexed.
        self.shadow.match_atoms(pattern)
    }

    fn get_atoms(&self) -> Vec<Atom> {
        self.shadow.get_atoms()
    }

    fn description(&self) -> &str { "MorkSpace (PathMap trie + indexed shadow)" }
}

// ========================================================================
// Pattern matching (shared by LocalSpace and MorkSpace fallback)
// ========================================================================

/// Try to match a query `pattern` against a stored `atom`.
///
/// Returns `Some(MatchResult)` on success, `None` on mismatch.
///
/// Two kinds of binding are collected:
/// - `query_bindings`: `Var(name)` in the query pattern → matched stored atom.
/// - `stored_bindings`: `$var` symbols IN the stored atom (Prolog-style unification
///   variables) → value from the query pattern. These are substituted throughout
///   the returned atom and query bindings so the caller gets fully ground values.
fn match_one(pattern: &Pattern, atom: &Atom) -> Option<MatchResult> {
    let mut query_bindings: Vec<(String, Atom)> = Vec::new();
    let mut stored_bindings: Vec<(String, Atom)> = Vec::new();
    if unify(pattern, atom, &mut query_bindings, &mut stored_bindings) {
        // Apply stored-var substitutions to query bindings so bound $vars in the
        // matched atom (e.g. $L, $a, $b in a function body) have concrete values.
        let bindings = query_bindings
            .into_iter()
            .map(|(n, v)| (n, substitute_stored(&v, &stored_bindings)))
            .collect();
        Some(MatchResult {
            atom: substitute_stored(atom, &stored_bindings),
            bindings,
        })
    } else {
        None
    }
}

/// Recursive unify: populates `query_bindings` (for Var patterns) and
/// `stored_bindings` (for $var atoms in the stored side).
fn unify(
    pattern: &Pattern,
    atom: &Atom,
    query_bindings: &mut Vec<(String, Atom)>,
    stored_bindings: &mut Vec<(String, Atom)>,
) -> bool {
    // Stored atom is a $var (Prolog-style wildcard) — unless the pattern is
    // Any/Var, bind the stored var to what the pattern specifies.
    if let Atom::Sym(s) = atom {
        if s.starts_with('$') && !matches!(pattern, Pattern::Any | Pattern::Var(_)) {
            let pat_atom = pattern_to_atom(pattern);
            if let Some((_, bound)) = stored_bindings.iter().find(|(n, _)| n == s) {
                return bound == &pat_atom;
            }
            stored_bindings.push((s.clone(), pat_atom));
            return true;
        }
    }
    match pattern {
        Pattern::Any => true,
        Pattern::Var(name) => {
            // Non-linear: if already bound, must equal
            if let Some((_, bound)) = query_bindings.iter().find(|(n, _)| n == name) {
                bound == atom
            } else {
                query_bindings.push((name.clone(), atom.clone()));
                true
            }
        }
        Pattern::Exact(expected) => atoms_equal(expected, atom),
        Pattern::Expr(pats) => match atom {
            Atom::Expr(items) => {
                if pats.len() != items.len() {
                    return false;
                }
                pats.iter()
                    .zip(items.iter())
                    .all(|(p, a)| unify(p, a, query_bindings, stored_bindings))
            }
            _ => false,
        },
    }
}

/// Substitute stored-var bindings throughout an atom tree.
fn substitute_stored(atom: &Atom, bindings: &[(String, Atom)]) -> Atom {
    match atom {
        Atom::Sym(s) if s.starts_with('$') => bindings
            .iter()
            .find(|(name, _)| name == s)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| atom.clone()),
        Atom::Expr(items) => {
            Atom::Expr(items.iter().map(|a| substitute_stored(a, bindings)).collect())
        }
        _ => atom.clone(),
    }
}

/// Convert a query pattern back to an Atom (used when a stored $var must
/// be bound to a pattern value, e.g. `Pattern::Exact(Num(2))` → `Atom::Num(2)`).
fn pattern_to_atom(pattern: &Pattern) -> Atom {
    match pattern {
        Pattern::Any => Atom::sym("_"),
        Pattern::Var(name) => Atom::sym(name),
        Pattern::Exact(a) => a.clone(),
        Pattern::Expr(pats) => Atom::Expr(pats.iter().map(pattern_to_atom).collect()),
    }
}

/// Deep structural equality for atoms.
fn atoms_equal(a: &Atom, b: &Atom) -> bool {
    match (a, b) {
        (Atom::Sym(a), Atom::Sym(b)) => a == b,
        (Atom::Num(a), Atom::Num(b)) => a == b,
        (Atom::Expr(a_items), Atom::Expr(b_items)) => {
            a_items.len() == b_items.len()
                && a_items.iter().zip(b_items.iter()).all(|(x, y)| atoms_equal(x, y))
        }
        _ => false,
    }
}

/// Parse a single S-expression string into an Atom.
pub fn parse_one_atom(input: &str) -> Result<Atom, String> {
    let input = input.trim();
    if input.is_empty() {
        return Err("empty input".into());
    }
    let chars: Vec<char> = input.chars().collect();
    let mut pos = 0;
    parse_value(&chars, &mut pos)
}

fn parse_value(chars: &[char], pos: &mut usize) -> Result<Atom, String> {
    skip_whitespace(chars, pos);
    if *pos >= chars.len() {
        return Err("unexpected end".into());
    }
    match chars[*pos] {
        '(' => {
            *pos += 1; // consume '('
            let mut items = Vec::new();
            loop {
                skip_whitespace(chars, pos);
                if *pos >= chars.len() {
                    return Err("unexpected end inside list".into());
                }
                if chars[*pos] == ')' {
                    *pos += 1; // consume ')'
                    return Ok(Atom::Expr(items));
                }
                items.push(parse_value(chars, pos)?);
            }
        }
        '"' => {
            *pos += 1; // consume '"'
            let mut s = String::new();
            while *pos < chars.len() && chars[*pos] != '"' {
                s.push(chars[*pos]);
                *pos += 1;
            }
            if *pos >= chars.len() {
                return Err("unterminated string".into());
            }
            *pos += 1; // consume '"'
            Ok(Atom::Sym(s))
        }
        '-' | '0'..='9' => {
            let start = *pos;
            if chars[*pos] == '-' {
                *pos += 1;
            }
            while *pos < chars.len() && chars[*pos].is_ascii_digit() {
                *pos += 1;
            }
            let num_str: String = chars[start..*pos].iter().collect();
            let n: i128 = num_str.parse().map_err(|_| format!("invalid number: {}", num_str))?;
            Ok(Atom::Num(n))
        }
        c if c.is_alphanumeric() || "$!?<>=+-*/_".contains(c) => {
            let start = *pos;
            while *pos < chars.len()
                && (chars[*pos].is_alphanumeric()
                    || "$!?<>=+-*/_".contains(chars[*pos]))
            {
                *pos += 1;
            }
            let sym: String = chars[start..*pos].iter().collect();
            Ok(Atom::Sym(sym))
        }
        c => Err(format!("unexpected character '{}'", c)),
    }
}

fn skip_whitespace(chars: &[char], pos: &mut usize) {
    while *pos < chars.len() && chars[*pos].is_whitespace() {
        *pos += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_space_add_match() {
        let mut space = LocalSpace::new();
        space.add_atom(&Atom::expr(vec![Atom::sym("friend"), Atom::sym("sam"), Atom::sym("tim")])).unwrap();
        space.add_atom(&Atom::expr(vec![Atom::sym("friend"), Atom::sym("sam"), Atom::sym("joe")])).unwrap();

        let pat = Pattern::Expr(vec![
            Pattern::Exact(Atom::sym("friend")),
            Pattern::Exact(Atom::sym("sam")),
            Pattern::Any,
        ]);
        let results = space.match_atoms(&pat);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_parse_one_atom_roundtrip() {
        let atom = Atom::expr(vec![Atom::sym("fib"), Atom::Num(30)]);
        let s = atom.to_sexpr_string();
        let parsed = parse_one_atom(&s).unwrap();
        assert_eq!(parsed, atom);
    }

    #[test]
    fn test_pattern_from_expr() {
        use crate::parser::parse_forms;
        let forms = parse_forms("!(friend sam $x)").unwrap();
        use crate::parser::TopForm;
        let expr = match &forms[0] {
            TopForm::Runnable(e) => e,
            _ => panic!("expected runnable"),
        };
        let pat = Pattern::from_expr(expr);
        match pat {
            Pattern::Expr(ref items) => {
                assert_eq!(items.len(), 3);
                assert!(matches!(items[2], Pattern::Var(_)));
            }
            _ => panic!("expected Expr pattern"),
        }
    }
}
