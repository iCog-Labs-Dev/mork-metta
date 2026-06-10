/// Atom storage backends for the MeTTa evaluator.
///
/// The `Space` trait is the core abstraction: a store of S-expression atoms
/// that supports add, remove, match, and enumeration.
///
/// Two implementations:
/// - `LocalSpace` — simple `Vec`-based storage (no dependencies)
/// - `MorkSpace` — wraps MORK's `PathMap` trie (requires `mork` feature)

use crate::atom::Atom;
use crate::parser::Expr;

/// A pattern for matching against atoms in a space.
///
/// Supports:
/// - `Any` — matches anything, no binding
/// - `Exact(a)` — matches the exact atom `a`
/// - `Expr(pats)` — matches an `Atom::Expr` where each element matches recursively
///
/// (Variables are not needed here — they're handled at the evaluator level
/// by converting `$x` symbol atoms into `Any` during query construction.)
#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Exact(Atom),
    Expr(Vec<Pattern>),
}

impl Pattern {
    /// Construct a pattern from a parsed Expr tree.
    /// Variables ($-prefixed symbols) become `Any`.
    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Symbol(s) if s.starts_with('$') => Pattern::Any,
            Expr::Symbol(s) => Pattern::Exact(Atom::Sym(s.clone())),
            Expr::Number(n) => Pattern::Exact(Atom::Num(*n)),
            Expr::List(items) => {
                Pattern::Expr(items.iter().map(Self::from_expr).collect())
            }
        }
    }
}

/// A match result: the matched atom plus variable bindings.
#[derive(Clone, Debug)]
pub struct MatchResult {
    pub atom: Atom,
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
// LocalSpace — simple Vec-based storage, no dependencies
// ========================================================================

/// A simple in-memory space backed by a `Vec<Atom>`.
/// Used when the `mork` feature is not available.
#[derive(Clone)]
pub struct LocalSpace {
    atoms: Vec<Atom>,
}

impl LocalSpace {
    pub fn new() -> Self {
        LocalSpace { atoms: Vec::new() }
    }
}

impl Space for LocalSpace {
    fn add_atom(&mut self, atom: &Atom) -> Result<(), String> {
        self.atoms.push(atom.clone());
        Ok(())
    }

    fn remove_atom(&mut self, atom: &Atom) -> Result<bool, String> {
        let len_before = self.atoms.len();
        self.atoms.retain(|a| a != atom);
        Ok(self.atoms.len() != len_before)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        let mut results = Vec::new();
        for atom in &self.atoms {
            let mut bindings = Vec::new();
            if unify(pattern, atom, &mut bindings) {
                results.push(MatchResult {
                    atom: atom.clone(),
                    bindings,
                });
            }
        }
        results
    }

    fn get_atoms(&self) -> Vec<Atom> {
        self.atoms.clone()
    }

    fn description(&self) -> &str {
        "LocalSpace (Vec)"
    }
}

// ========================================================================
// MorkSpace — wraps MORK's PathMap trie
// ========================================================================

/// Space backed by MORK's hypergraph trie.
///
/// Atoms are serialized to S-expression strings for MORK's text-based API,
/// and results are parsed back into our `Atom` type.
#[cfg(feature = "mork")]
pub struct MorkSpace {
    inner: mork::space::Space<mork::weightedsweep::U64AtomHeader>,
}

#[cfg(feature = "mork")]
impl MorkSpace {
    pub fn new() -> Self {
        MorkSpace {
            inner: mork::space::Space::new(),
        }
    }
}

#[cfg(feature = "mork")]
impl Space for MorkSpace {
    fn add_atom(&mut self, atom: &Atom) -> Result<(), String> {
        let sexpr = atom.to_sexpr_string();
        self.inner.add_all_sexpr(sexpr.as_bytes())?;
        Ok(())
    }

    fn remove_atom(&mut self, atom: &Atom) -> Result<bool, String> {
        let sexpr = atom.to_sexpr_string();
        let count = self.inner.remove_all_sexpr(sexpr.as_bytes())?;
        Ok(count > 0)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        // Build a query string: "(<pattern> _1)" where _1 captures the match
        // We need MORK's Expr type for this. Use the space's parser.
        // For now, fall back to a simple approach: get all atoms and filter
        let all = self.get_atoms();
        let mut results = Vec::new();
        for atom in &all {
            let mut bindings = Vec::new();
            if unify(pattern, atom, &mut bindings) {
                results.push(MatchResult {
                    atom: atom.clone(),
                    bindings,
                });
            }
        }
        results
    }

    fn get_atoms(&self) -> Vec<Atom> {
        let mut buf = Vec::new();
        if self.inner.dump_all_sexpr(&mut buf).is_err() {
            return Vec::new();
        }
        let text = String::from_utf8(buf).unwrap_or_default();
        text.lines()
            .filter_map(|line| {
                let line = line.trim();
                if line.is_empty() {
                    return None;
                }
                parse_one_atom(line).ok()
            })
            .collect()
    }

    fn description(&self) -> &str {
        "MorkSpace (PathMap trie)"
    }
}

// ========================================================================
// Pattern matching (shared by LocalSpace and MorkSpace fallback)
// ========================================================================

/// Recursive pattern matching: does `pattern` match `atom`?
/// If so, populate `bindings` with variable bindings.
fn unify(pattern: &Pattern, atom: &Atom, bindings: &mut Vec<(String, Atom)>) -> bool {
    match pattern {
        Pattern::Any => true,

        Pattern::Exact(expected) => atoms_equal(expected, atom),

        Pattern::Expr(pats) => match atom {
            Atom::Expr(items) => {
                if pats.len() != items.len() {
                    return false;
                }
                pats.iter()
                    .zip(items.iter())
                    .all(|(p, a)| unify(p, a, bindings))
            }
            _ => false,
        },
    }
}

/// Deep equality for atoms.
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
            let n: i64 = num_str.parse().map_err(|_| format!("invalid number: {}", num_str))?;
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
                assert!(matches!(items[2], Pattern::Any));
            }
            _ => panic!("expected Expr pattern"),
        }
    }
}
