/// Atom storage backends for the MeTTa evaluator.
///
/// The `Space` trait is the core abstraction: a store of S-expression atoms
/// that supports add, remove, match, and enumeration.
///
/// Two implementations:
/// - `LocalSpace` — simple `Vec`-based storage (no dependencies)
/// - `MorkSpace` — wraps MORK's `PathMap` trie (requires `mork` feature)

use std::collections::HashMap;
use std::sync::RwLock;
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
// LocalSpace — HashMap-indexed storage, no dependencies
// ========================================================================

/// Extract the index key `(functor, list_len)` for an atom, if it has one.
/// Only `Atom::Expr` starting with a `Sym` is indexable.
fn index_key(atom: &Atom) -> Option<(String, usize)> {
    if let Atom::Expr(items) = atom {
        if let Some(Atom::Sym(f)) = items.first() {
            return Some((f.to_string(), items.len()));
        }
    }
    None
}

/// Extract the index key a pattern can use for O(1) candidate lookup.
/// Returns `None` when the first position is a wildcard/variable — full scan required.
fn pattern_index_key(pattern: &Pattern) -> Option<(String, usize)> {
    match pattern {
        Pattern::Expr(pats) => match pats.first()? {
            Pattern::Exact(Atom::Sym(f)) => Some((f.to_string(), pats.len())),
            _ => None,
        },
        Pattern::Exact(Atom::Expr(items)) => match items.first()? {
            Atom::Sym(f) => Some((f.to_string(), items.len())),
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
#[derive(Default)]
pub struct LocalSpace {
    indexed: std::sync::Mutex<HashMap<(String, usize), Vec<Atom>>>,
    scalars: std::sync::Mutex<Vec<Atom>>,
    /// O(1) existence check for exact atom membership.
    has: std::sync::Mutex<std::collections::HashSet<Atom>>,
}

impl LocalSpace {
    pub fn new() -> Self { Self::default() }
    pub fn new_box() -> Box<dyn Space + Send + Sync> { Box::new(Self::default()) }
}

impl Space for LocalSpace {
    fn add_atom(&self, atom: &Atom) -> Result<(), String> {
        self.has.lock().unwrap().insert(atom.clone());
        if let Some(key) = index_key(atom) {
            self.indexed.lock().unwrap().entry(key).or_default().push(atom.clone());
        } else {
            self.scalars.lock().unwrap().push(atom.clone());
        }
        Ok(())
    }

    fn remove_atom(&self, atom: &Atom) -> Result<bool, String> {
        self.has.lock().unwrap().remove(atom);
        if let Some(key) = index_key(atom) {
            if let Some(vec) = self.indexed.lock().unwrap().get_mut(&key) {
                let before = vec.len();
                vec.retain(|a| a != atom);
                let removed = vec.len() < before;
                if vec.is_empty() { self.indexed.lock().unwrap().remove(&key); }
                return Ok(removed);
            }
            return Ok(false);
        }
        let before = self.scalars.lock().unwrap().len();
        self.scalars.lock().unwrap().retain(|a| a != atom);
        Ok(self.scalars.lock().unwrap().len() < before)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        // Fast path: fully ground pattern — O(1) hash lookup.
        if let Some(atom) = pattern.as_ground_atom() {
            return if self.has.lock().unwrap().contains(&atom) {
                vec![MatchResult { atom, bindings: vec![] }]
            } else {
                vec![]
            };
        }
        let indexed = self.indexed.lock().unwrap();
        let scalars = self.scalars.lock().unwrap();

        // Indexed path: resolve functor+arity bucket and scan only that bucket.
        if let Some(key) = pattern_index_key(pattern) {
            return indexed.get(&key)
                .map(|atoms| atoms.iter().filter_map(|a| match_one(pattern, a)).collect())
                .unwrap_or_default();
        }
        // Full scan: wildcard or variable at functor position.
        indexed.values()
            .flat_map(|v| v.iter())
            .chain(scalars.iter())
            .filter_map(|a| match_one(pattern, a))
            .collect()
    }

    fn get_atoms(&self) -> Vec<Atom> {
        let indexed = self.indexed.lock().unwrap();
        let scalars = self.scalars.lock().unwrap();
        indexed.values()
            .flat_map(|v| v.iter().cloned())
            .chain(scalars.iter().cloned())
            .collect()
    }

    fn description(&self) -> &str { "LocalSpace (indexed by functor+arity)" }
}

// ========================================================================
// ShardedSpace — shard-by-bucket for concurrent read/write
// ========================================================================

/// Pick a shard index for an atom based on its index key hash.
/// Atoms without an index key use a fallback hash of the atom itself.
fn pick_shard(atom: &Atom, n_shards: usize) -> usize {
    use std::hash::{Hash, Hasher};
    let key = index_key(atom);
    let hash = match &key {
        Some((f, len)) => {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            f.hash(&mut h);
            len.hash(&mut h);
            h.finish()
        }
        None => {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            atom.hash(&mut h);
            h.finish()
        }
    };
    (hash as usize) % n_shards
}

/// Space sharded by `(functor, arity)` key hash for concurrent access.
///
/// Each shard is an independent `LocalSpace` behind its own `RwLock`.
/// - `add_atom` / `remove_atom` lock only the atom's shard (single-writer).
/// - `match_atoms` with an index key queries one shard (no cross-shard scan).
/// - `match_atoms` for wildcards fans out to all shards in parallel via Rayon.
/// - Multiple readers can coexist (readers don't block each other).
///
/// The default shard count matches the number of CPU cores.
pub struct ShardedSpace {
    n_shards: usize,
    shards: Vec<RwLock<LocalSpace>>,
}

impl ShardedSpace {
    /// Create a new sharded space with `n` shards.
    pub fn new(n: usize) -> Self {
        let n_shards = n.max(1);
        let mut shards = Vec::with_capacity(n_shards);
        for _ in 0..n_shards {
            shards.push(RwLock::new(LocalSpace::new()));
        }
        ShardedSpace { n_shards, shards }
    }

    /// Create a new sharded space with one shard per CPU core.
    pub fn new_default() -> Self {
        Self::new(std::thread::available_parallelism()
            .map(|n| n.get()).unwrap_or(4))
    }

    pub fn new_box(n: usize) -> Box<dyn Space + Send> {
        Box::new(Self::new(n))
    }
}

impl Space for ShardedSpace {
    fn add_atom(&self, atom: &Atom) -> Result<(), String> {
        let shard = pick_shard(atom, self.n_shards);
        self.shards[shard].write().unwrap().add_atom(atom)
    }

    fn remove_atom(&self, atom: &Atom) -> Result<bool, String> {
        let shard = pick_shard(atom, self.n_shards);
        self.shards[shard].write().unwrap().remove_atom(atom)
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        if let Some(key) = pattern_index_key(pattern) {
            // Indexed pattern: only query the relevant shard
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            key.0.hash(&mut h);
            key.1.hash(&mut h);
            let shard = (h.finish() as usize) % self.n_shards;
            return self.shards[shard].read().unwrap().match_atoms(pattern);
        }
        // Full scan: query all shards in parallel, merge results
        use rayon::prelude::*;
        self.shards.par_iter()
            .flat_map(|s| s.read().unwrap().match_atoms(pattern))
            .collect()
    }

    fn get_atoms(&self) -> Vec<Atom> {
        // Lock each shard sequentially (parallel would be worse due to contention)
        let mut all = Vec::new();
        for shard in &self.shards {
            all.extend(shard.read().unwrap().get_atoms());
        }
        all
    }

    fn description(&self) -> &str { "ShardedSpace (concurrent, shard-by-bucket)" }
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
    inner: std::sync::Mutex<mork::space::Space<mork::weightedsweep::U64AtomHeader>>,
    /// Mirrors `inner` in Rust form — serves all read operations without going
    /// through the serialization round-trip.
    shadow: LocalSpace,
    /// Reusable scratch for encoding atoms into trie paths. Avoids the kernel
    /// bulk-load path (`add_all_sexpr`), which allocates a 4GiB scratch Vec
    /// and runs a multi-expression parse loop for every single atom.
    encode_buf: std::sync::Mutex<Vec<u8>>,
}

#[cfg(feature = "mork")]
impl MorkSpace {
    pub fn new() -> Self {
        MorkSpace {
            inner: std::sync::Mutex::new(mork::space::Space::new()),
            shadow: LocalSpace::new(),
            encode_buf: std::sync::Mutex::new(vec![0u8; 1 << 16]),
        }
    }

    /// Encode one atom into the trie's byte format using the reusable buffer.
    /// Returns the encoded length.
    fn encode_atom(&self, atom: &Atom) -> Result<usize, String> {
        let sexpr = atom.to_sexpr_string();
        // Worst case: every byte of text becomes an 8-byte interned symbol + tag.
        let cap = sexpr.len() * 8 + 64;
        let mut buf = self.encode_buf.lock().unwrap();
        if cap > buf.len() {
            buf.resize(cap, 0);
        }
        let mut inner = self.inner.lock().unwrap();
        let (_expr, len) = inner
            .parse_sexpr(sexpr.as_bytes(), buf.as_mut_ptr())
            .map_err(|e| format!("mork parse: {:?}", e))?;
        Ok(len)
    }
}

#[cfg(feature = "mork")]
impl Space for MorkSpace {
    fn add_atom(&self, atom: &Atom) -> Result<(), String> {
        let len = self.encode_atom(atom)?;
        let buf = self.encode_buf.lock().unwrap();
        self.inner.lock().unwrap().btm.insert(&buf[..len], Default::default());
        drop(buf);
        self.shadow.add_atom(atom)
    }

    fn remove_atom(&self, atom: &Atom) -> Result<bool, String> {
        let len = self.encode_atom(atom)?;
        let buf = self.encode_buf.lock().unwrap();
        let removed = self.inner.lock().unwrap().btm.remove(&buf[..len]).is_some();
        drop(buf);
        self.shadow.remove_atom(atom)?;
        Ok(removed)
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
