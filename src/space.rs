/// Atom storage backends for the MeTTa evaluator.
///
/// The `Space` trait is the core abstraction: a store of S-expression atoms
/// that supports add, remove, match, and enumeration.
///
/// Single implementation:
/// - `MorkSpace` — wraps MORK's `PathMap` trie (the single source of truth).

use crate::atom::Atom;
use crate::parser::Expr;

use pathmap::zipper::{ZipperMoving, ZipperIteration, ZipperAbsolutePath};

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
    /// If this pattern is fully ground (no Var or Any nodes), recover the
    /// concrete `Atom` it represents. Used for fast-path exact lookups.
    pub fn as_ground_atom(&self) -> Option<Atom> {
        match self {
            Pattern::Any | Pattern::Var(_) => None,
            Pattern::Exact(a) => Some(a.clone()),
            Pattern::Expr(pats) => {
                pats.iter()
                    .map(|p| p.as_ground_atom())
                    .collect::<Option<Vec<_>>>()
                    .map(Atom::Expr)
            }
        }
    }

    /// Construct a pattern from a parsed Expr tree.
    /// `$`-prefixed symbols become `Var(name)`; others become `Exact`.
    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Symbol(s) if s.starts_with('$') => Pattern::Var(s.clone()),
            Expr::Symbol(s) => Pattern::Exact(Atom::sym(s)),
            Expr::Number(n) => Pattern::Exact(Atom::Num(*n)),
            Expr::List(items) => {
                Pattern::Expr(items.iter().map(Self::from_expr).collect())
            }
        }
    }

    /// Construct a pattern from a runtime Atom (e.g. a pattern passed through a function arg).
    /// `$`-prefixed Sym atoms become `Var(name)`; others become `Exact`.
    pub fn from_atom(atom: &Atom) -> Self {
        match atom {
            Atom::Sym(s) if s.starts_with('$') => Pattern::Var(s.to_string()),
            Atom::Sym(_) | Atom::Num(_) => Pattern::Exact(atom.clone()),
            Atom::Expr(items) => Pattern::Expr(items.iter().map(Self::from_atom).collect()),
            _ => Pattern::Exact(atom.clone()),
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
/// Uses interior mutability (&self for all methods) to enable RwLock<Box<dyn Space>>.
pub trait Space: Send + Sync {
    /// Add an atom to the space. Interior mutability handles actual mutation.
    fn add_atom(&self, atom: &Atom) -> Result<(), String>;

    /// Remove an atom from the space. Returns true if something was removed.
    fn remove_atom(&self, atom: &Atom) -> Result<bool, String>;

    /// Match atoms against a pattern. Returns all matching atoms and bindings.
    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult>;

    /// Return all atoms in the space.
    fn get_atoms(&self) -> Vec<Atom>;

    /// Return a human-readable description of the backend.
    fn description(&self) -> &str;
}

// ========================================================================
// MorkSpace — wraps MORK's PathMap trie
// ========================================================================

/// Space backed by MORK's PathMap trie as the **single source of truth**.
///
/// There is no shadow store. Writes byte-encode the atom and `insert`/`remove`
/// it in the trie. Reads traverse the trie directly:
/// - `match_atoms` narrows to the subtree sharing the pattern's constant byte
///   prefix (`Expr::prefix` → `read_zipper_at_path`), so a pattern like
///   `(= (fib $n) $b)` only visits stored `(= (fib …) …)` paths — the real
///   PathMap prefix-sharing win — then decodes each candidate and runs the
///   named unifier to extract `$`-bindings.
/// - `get_atoms` walks the whole trie.
///
/// NOTE: the kernel `query_multi`/`dump_sexpr` paths reserve a multi-GiB path
/// buffer per call (built for bulk transforms), so they are deliberately NOT
/// used for interactive per-term lookup. A plain `read_zipper` traversal is the
/// cheap primitive.
///
/// Variables round-trip as positional MORK vars (`$a`, `$b`, …) — alpha-
/// equivalent to the source names, which is all unification requires.
pub struct MorkSpace {
    inner: std::sync::Mutex<mork::space::Space<mork::weightedsweep::U64AtomHeader>>,
    /// Reusable scratch for encoding atoms/patterns into trie paths.
    encode_buf: std::sync::Mutex<Vec<u8>>,
}

impl MorkSpace {
    pub fn new() -> Self {
        MorkSpace {
            inner: std::sync::Mutex::new(mork::space::Space::new()),
            encode_buf: std::sync::Mutex::new(vec![0u8; 1 << 16]),
        }
    }

    pub fn new_box() -> Box<dyn Space + Send + Sync> { Box::new(Self::new()) }

    /// Byte-encode an s-expression into `buf` via the kernel parser.
    /// Returns the encoded length. Symbols are stored literally (no interning
    /// in this build), so the same bytes decode back via `Expr::serialize2`.
    fn encode_into(
        buf: &mut Vec<u8>,
        inner: &mut mork::space::Space<mork::weightedsweep::U64AtomHeader>,
        sexpr: &str,
    ) -> Result<usize, String> {
        // Worst case: every text byte becomes a tagged symbol entry.
        let cap = sexpr.len() * 8 + 64;
        if cap > buf.len() {
            buf.resize(cap, 0);
        }
        let (_expr, len) = inner
            .parse_sexpr(sexpr.as_bytes(), buf.as_mut_ptr())
            .map_err(|e| format!("mork parse: {:?}", e))?;
        Ok(len)
    }
}

impl Space for MorkSpace {
    fn add_atom(&self, atom: &Atom) -> Result<(), String> {
        let sexpr = atom.to_sexpr_string();
        let mut buf = self.encode_buf.lock().unwrap();
        let mut inner = self.inner.lock().unwrap();
        let len = Self::encode_into(&mut buf, &mut inner, &sexpr)?;
        inner.btm.insert(&buf[..len], Default::default());
        Ok(())
    }

    fn remove_atom(&self, atom: &Atom) -> Result<bool, String> {
        let sexpr = atom.to_sexpr_string();
        let mut buf = self.encode_buf.lock().unwrap();
        let mut inner = self.inner.lock().unwrap();
        let len = Self::encode_into(&mut buf, &mut inner, &sexpr)?;
        Ok(inner.btm.remove(&buf[..len]).is_some())
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        // Ground fast-path: exact existence check, O(key length).
        if let Some(atom) = pattern.as_ground_atom() {
            let sexpr = atom.to_sexpr_string();
            let mut buf = self.encode_buf.lock().unwrap();
            let mut inner = self.inner.lock().unwrap();
            let len = match Self::encode_into(&mut buf, &mut inner, &sexpr) {
                Ok(l) => l,
                Err(_) => return vec![],
            };
            return if inner.btm.get_val_at(&buf[..len]).is_some() {
                vec![MatchResult { atom, bindings: vec![] }]
            } else {
                vec![]
            };
        }

        // Non-ground: narrow the trie by the pattern's constant byte prefix,
        // traverse that subtree only, decode each stored atom, and run the
        // named unifier for $-bindings.
        let query_sexpr = pattern_to_query_sexpr(pattern);
        let mut buf = self.encode_buf.lock().unwrap();
        let mut inner = self.inner.lock().unwrap();
        let prefix: &[u8] = match inner.parse_sexpr(query_sexpr.as_bytes(), buf.as_mut_ptr()) {
            // prefix() = Ok(proper prefix before first var) | Err(full span).
            Ok((e, _len)) => match e.prefix() {
                Ok(p) | Err(p) => unsafe { &*p },
            },
            // Parse failure → fall back to a full traversal (empty prefix).
            Err(_) => &[],
        };

        let mut results = Vec::new();
        let mut z = inner.btm.read_zipper_at_path(prefix);
        while z.to_next_val() {
            // origin_path = prefix ++ path = the full stored key (encoded atom).
            if let Some(stored) = decode_expr_bytes(z.origin_path()) {
                if let Some(mr) = match_one(pattern, &stored) {
                    results.push(mr);
                }
            }
        }
        results
    }

    fn get_atoms(&self) -> Vec<Atom> {
        let inner = self.inner.lock().unwrap();
        let mut out = Vec::new();
        let mut z = inner.btm.read_zipper();
        while z.to_next_val() {
            if let Some(a) = decode_expr_bytes(z.path()) {
                out.push(a);
            }
        }
        out
    }

    fn description(&self) -> &str { "MorkSpace (PathMap trie, single source of truth)" }
}

/// Render a `Pattern` as a MORK query s-expression: variables/wildcards become
/// `$` (positional new-vars), exact atoms render literally. Used only to derive
/// the constant byte prefix for trie narrowing.
fn pattern_to_query_sexpr(p: &Pattern) -> String {
    match p {
        Pattern::Any | Pattern::Var(_) => "$".to_string(),
        Pattern::Exact(a) => a.to_sexpr_string(),
        Pattern::Expr(ps) => {
            let inner: Vec<String> = ps.iter().map(pattern_to_query_sexpr).collect();
            format!("({})", inner.join(" "))
        }
    }
}

/// Decode a trie key (byte-encoded expression) directly into an `Atom`,
/// without a serialize→string→parse round-trip.
///
/// Symbols are stored literally (no interning in this build). Positional MORK
/// variables render as `$a`, `$b`, … (`Expr::VARNAMES`), with `NewVar`s numbered
/// in pre-order — matching what the kernel's own serializer would emit, so the
/// produced `Atom` is identical to the former parse-based path. Numeric symbols
/// map to `Atom::Num` per the same rule as `parser::parse_value`.
fn decode_expr_bytes(bytes: &[u8]) -> Option<Atom> {
    if bytes.is_empty() {
        return None;
    }
    let mut pos = 0usize;
    let mut var_count: u8 = 0;
    decode_one(bytes, &mut pos, &mut var_count)
}

fn varname(i: u8) -> Atom {
    Atom::sym(mork_expr::Expr::VARNAMES.get(i as usize).copied().unwrap_or("$z"))
}

/// A literal symbol token → `Num` if it is an integer literal, else `Sym`.
/// Mirrors `parser::parse_value`: optional leading `-` then ASCII digits.
fn symbol_to_atom(s: &str) -> Atom {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if !digits.is_empty() && digits.bytes().all(|c| c.is_ascii_digit()) {
        if let Ok(n) = s.parse::<i128>() {
            return Atom::Num(n);
        }
    }
    Atom::sym(s)
}

fn decode_one(b: &[u8], pos: &mut usize, var_count: &mut u8) -> Option<Atom> {
    use mork_expr::{byte_item, Tag, read_arity_at, arity_byte_count_at};
    if *pos >= b.len() {
        return None;
    }
    match byte_item(b[*pos]) {
        Tag::NewVar => {
            let idx = *var_count;
            *var_count = var_count.saturating_add(1);
            *pos += 1;
            Some(varname(idx))
        }
        Tag::VarRef(i) => {
            *pos += 1;
            Some(varname(i))
        }
        Tag::SymbolSize(s) => {
            *pos += 1;
            let s = s as usize;
            if *pos + s > b.len() {
                return None;
            }
            let sym = std::str::from_utf8(&b[*pos..*pos + s]).ok()?;
            *pos += s;
            Some(symbol_to_atom(sym))
        }
        Tag::Arity(n) => {
            *pos += 1;
            decode_children(b, pos, var_count, n as usize)
        }
        Tag::LongArity => {
            let n = read_arity_at(b[*pos..].as_ptr()) as usize;
            *pos += arity_byte_count_at(b[*pos..].as_ptr());
            decode_children(b, pos, var_count, n)
        }
    }
}

fn decode_children(b: &[u8], pos: &mut usize, var_count: &mut u8, n: usize) -> Option<Atom> {
    let mut items = Vec::with_capacity(n);
    for _ in 0..n {
        items.push(decode_one(b, pos, var_count)?);
    }
    Some(Atom::Expr(items))
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
            if let Some((_, bound)) = stored_bindings.iter().find(|(n, _)| n.as_str() == s.as_ref()) {
                return bound == &pat_atom;
            }
            stored_bindings.push((s.to_string(), pat_atom));
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
            .find(|(name, _)| name.as_str() == s.as_ref())
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
            Ok(Atom::sym(&s))
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
            Ok(Atom::sym(&sym))
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
    fn test_mork_space_add_match() {
        let space = MorkSpace::new();
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
