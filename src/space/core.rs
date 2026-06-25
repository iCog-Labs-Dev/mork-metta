//! Core space abstraction: trait, backend implementation, and pattern types.
//!
//! Mirrors `src/space.rs`. Lives here so the staged tree is self-contained
//! and `crate::space::Space` / `crate::space::MorkSpace` resolve correctly
//! after the swap.

use crate::atom::Atom;
use crate::parser::Expr;
use std::sync::Arc;
use mork_frontend::bytestring_parser::Parser;

use pathmap::zipper::{ZipperAbsolutePath, ZipperIteration, ZipperMoving};

#[derive(Clone, Debug)]
pub enum Pattern {
    Any,
    Var(String),
    Exact(Atom),
    Expr(Vec<Pattern>),
}

impl Pattern {
    pub fn as_ground_atom(&self) -> Option<Atom> {
        match self {
            Pattern::Any | Pattern::Var(_) => None,
            Pattern::Exact(a) => Some(a.clone()),
            Pattern::Expr(pats) => pats
                .iter()
                .map(|p| p.as_ground_atom())
                .collect::<Option<Vec<_>>>()
                .map(|v| Atom::Expr(crate::atom::expr_data(v))),
        }
    }

    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Symbol(s) if s.starts_with('$') => Pattern::Var(s.clone()),
            Expr::Symbol(s) => Pattern::Exact(Atom::sym(s)),
            Expr::Str(s) => Pattern::Exact(Atom::str_val(s)),
            Expr::Number(n) => Pattern::Exact(Atom::Num(n.clone())),
            Expr::List(items) => Pattern::Expr(items.iter().map(Self::from_expr).collect()),
        }
    }

    pub fn from_atom(atom: &Atom) -> Self {
        match atom {
            Atom::Sym(s) if s.starts_with('$') => Pattern::Var(s.to_string()),
            Atom::Sym(_) | Atom::Num(_) => Pattern::Exact(atom.clone()),
            Atom::Expr(items) => Pattern::Expr(items.iter().map(Self::from_atom).collect()),
            _ => Pattern::Exact(atom.clone()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MatchResult {
    pub atom: Atom,
    pub bindings: Vec<(Arc<str>, Arc<Atom>)>,
}

pub trait Space: Send + Sync {
    fn add_atom(&self, atom: &Atom) -> Result<(), String>;
    fn remove_atom(&self, atom: &Atom) -> Result<bool, String>;
    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult>;
    fn get_atoms(&self) -> Vec<Atom>;
    fn description(&self) -> &str;
}

// Per-thread encode buffer. Avoids a shared lock during the encode phase so
// multiple threads can each parse queries without contending on a single buffer.
thread_local! {
    static ENCODE_BUF: std::cell::RefCell<Vec<u8>> =
        std::cell::RefCell::new(vec![0u8; 1 << 16]);
}

// Per-thread encode buffer: each thread encodes its own query pattern without
// contending on a shared buffer, while the trie itself is read concurrently.
thread_local! {
    static MORK_SPACE_ENCODE_BUF: std::cell::RefCell<Vec<u8>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

pub struct MorkSpace {
    /// RwLock: ArenaCompactTree is now Sync (Cell moved to zipper), so concurrent
    /// reads are safe. Only add_atom/remove_atom take the write lock.
    inner: std::sync::RwLock<mork::space::Space<mork::weightedsweep::UnitHeader>>,
}

impl MorkSpace {
    pub fn new() -> Self {
        MorkSpace {
            inner: std::sync::RwLock::new(mork::space::Space::new()),
        }
    }

    pub fn new_box() -> Box<dyn Space + Send + Sync> {
        Box::new(Self::new())
    }

    fn encode_atom_direct(
        atom: &Atom,
        inner: &mork::space::Space<mork::weightedsweep::UnitHeader>,
        buf: &mut Vec<u8>,
    ) -> Result<usize, String> {
        let cap = approx_size(atom) + 64;
        if buf.len() < cap {
            buf.resize(cap, 0);
        }
        let sym_table = inner.sym_table();
        let mut pdp = mork::space::ParDataParser::new(&sym_table);
        let mut ez = mork_expr::ExprZipper::new(mork_expr::Expr { ptr: buf.as_mut_ptr() });
        let mut vars = Vec::new();
        encode_atom_inner(atom, &mut pdp, &mut ez, &mut vars)?;
        Ok(ez.loc)
    }

    fn encode_pattern_direct(
        pattern: &Pattern,
        inner: &mork::space::Space<mork::weightedsweep::UnitHeader>,
        buf: &mut Vec<u8>,
    ) -> Result<usize, String> {
        let cap = approx_pattern_size(pattern) + 64;
        if buf.len() < cap {
            buf.resize(cap, 0);
        }
        let sym_table = inner.sym_table();
        let mut pdp = mork::space::ParDataParser::new(&sym_table);
        let mut ez = mork_expr::ExprZipper::new(mork_expr::Expr { ptr: buf.as_mut_ptr() });
        let mut vars = Vec::new();
        encode_pattern_inner(pattern, &mut pdp, &mut ez, &mut vars)?;
        Ok(ez.loc)
    }
}

fn approx_size(atom: &Atom) -> usize {
    match atom {
        Atom::Sym(s) => s.len() + 2,
        Atom::Str(s) => s.len() + 10,
        Atom::Num(_) => 32,
        Atom::Expr(items) => 2 + items.iter().map(approx_size).sum::<usize>(),
        Atom::Closure(_) => 128,
        Atom::Gnd(_) => 128,
    }
}

fn approx_pattern_size(p: &Pattern) -> usize {
    match p {
        Pattern::Any | Pattern::Var(_) => 2,
        Pattern::Exact(a) => approx_size(a),
        Pattern::Expr(ps) => 2 + ps.iter().map(approx_pattern_size).sum::<usize>(),
    }
}

fn encode_atom_inner(
    atom: &Atom,
    pdp: &mut mork::space::ParDataParser,
    ez: &mut mork_expr::ExprZipper,
    vars: &mut Vec<String>,
) -> Result<(), String> {
    match atom {
        Atom::Sym(s) => {
            if s.starts_with('$') {
                if let Some(pos) = vars.iter().position(|v| v == s.as_ref()) {
                    ez.write_var_ref(pos as u8);
                    unsafe {
                        ez.loc += mork_expr::var_ref_byte_count_at(ez.root.ptr.byte_add(ez.loc));
                    }
                } else {
                    vars.push(s.to_string());
                    ez.write_new_var();
                    ez.loc += 1;
                }
            } else {
                let token = pdp.tokenizer(s.as_bytes());
                ez.write_symbol(token);
                ez.loc += token.len() + 1;
            }
        }
        Atom::Str(s) => {
            let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
            let quoted = format!("\"{}\"", escaped);
            let token = pdp.tokenizer(quoted.as_bytes());
            ez.write_symbol(token);
            ez.loc += token.len() + 1;
        }
        Atom::Num(n) => {
            let n_str = n.to_string();
            let token = pdp.tokenizer(n_str.as_bytes());
            ez.write_symbol(token);
            ez.loc += token.len() + 1;
        }
        Atom::Expr(items) => {
            let arity = items.len() as u64;
            ez.write_arity(arity);
            unsafe {
                ez.loc += mork_expr::arity_byte_count_at(ez.root.ptr.byte_add(ez.loc));
            }
            for item in items.iter() {
                encode_atom_inner(item, pdp, ez, vars)?;
            }
        }
        Atom::Closure(_) => {
            return Err("Cannot encode Closure in space".to_string());
        }
        Atom::Gnd(g) => {
            let s = g.display_metta();
            let token = pdp.tokenizer(s.as_bytes());
            ez.write_symbol(token);
            ez.loc += token.len() + 1;
        }
    }
    Ok(())
}

fn encode_pattern_inner(
    p: &Pattern,
    pdp: &mut mork::space::ParDataParser,
    ez: &mut mork_expr::ExprZipper,
    vars: &mut Vec<String>,
) -> Result<(), String> {
    match p {
        Pattern::Any | Pattern::Var(_) => {
            ez.write_new_var();
            ez.loc += 1;
        }
        Pattern::Exact(atom) => {
            encode_atom_inner(atom, pdp, ez, vars)?;
        }
        Pattern::Expr(ps) => {
            let arity = ps.len() as u64;
            ez.write_arity(arity);
            unsafe {
                ez.loc += mork_expr::arity_byte_count_at(ez.root.ptr.byte_add(ez.loc));
            }
            for item in ps.iter() {
                encode_pattern_inner(item, pdp, ez, vars)?;
            }
        }
    }
    Ok(())
}

impl Space for MorkSpace {
    fn add_atom(&self, atom: &Atom) -> Result<(), String> {
        //  write directly to the trie bytes instead of formatting to an sexpr string first
        MORK_SPACE_ENCODE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            let mut inner = self.inner.write().unwrap();
            let len = Self::encode_atom_direct(atom, &*inner, &mut buf)?;
            inner.btm.insert(&buf[..len], Default::default());
            Ok(())
        })
    }

    fn remove_atom(&self, atom: &Atom) -> Result<bool, String> {
        //  write directly to the trie bytes instead of formatting to an sexpr string first
        MORK_SPACE_ENCODE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            let mut inner = self.inner.write().unwrap();
            let len = Self::encode_atom_direct(atom, &*inner, &mut buf)?;
            Ok(inner.btm.remove(&buf[..len]).is_some())
        })
    }

    fn match_atoms(&self, pattern: &Pattern) -> Vec<MatchResult> {
        if let Some(atom) = pattern.as_ground_atom() {
            // Phase 1: encode (read lock — concurrent with other readers).
            let encoded: Vec<u8> = MORK_SPACE_ENCODE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                let inner = self.inner.read().unwrap();
                match Self::encode_atom_direct(&atom, &*inner, &mut buf) {
                    Ok(len) => buf[..len].to_vec(),
                    Err(_) => vec![],
                }
            });
            if encoded.is_empty() { return vec![]; }
            // Phase 2: lookup (read lock, concurrent with other readers).
            let inner = self.inner.read().unwrap();
            return if inner.btm.get_val_at(&encoded).is_some() {
                vec![MatchResult { atom, bindings: vec![] }]
            } else {
                vec![]
            };
        }

        // Phase 1: encode prefix (read lock — concurrent with other readers).
        let prefix_bytes: Vec<u8> = MORK_SPACE_ENCODE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            let inner = self.inner.read().unwrap();
            match Self::encode_pattern_direct(pattern, &*inner, &mut buf) {
                Ok(len) => {
                    let e = mork_expr::Expr { ptr: buf.as_mut_ptr() };
                    match e.prefix() {
                        Ok(p) | Err(p) => unsafe { &*p }.to_vec(),
                    }
                }
                Err(_) => vec![],
            }
        });

        // Phase 2: traverse (read lock — concurrent with other readers).
        let inner = self.inner.read().unwrap();
        let mut results = Vec::new();
        let mut z = inner.btm.read_zipper_at_path(&prefix_bytes);
        while z.to_next_val() {
            if let Some(stored) = decode_expr_bytes(z.origin_path()) {
                if let Some(mr) = match_one(pattern, &stored) {
                    results.push(mr);
                }
            }
        }

        if results.is_empty() && !prefix_bytes.is_empty() {
            let mut z = inner.btm.read_zipper();
            while z.to_next_val() {
                if let Some(stored) = decode_expr_bytes(z.origin_path()) {
                    if let Some(mr) = match_one(pattern, &stored) {
                        results.push(mr);
                    }
                }
            }
        }

        results
    }

    fn get_atoms(&self) -> Vec<Atom> {
        let inner = self.inner.read().unwrap();
        let mut out = Vec::new();
        let mut z = inner.btm.read_zipper();
        while z.to_next_val() {
            if let Some(a) = decode_expr_bytes(z.path()) {
                out.push(a);
            }
        }
        out
    }

    fn description(&self) -> &str {
        "MorkSpace (PathMap trie, single source of truth)"
    }
}

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

fn decode_expr_bytes(bytes: &[u8]) -> Option<Atom> {
    if bytes.is_empty() {
        return None;
    }
    let mut pos = 0usize;
    let mut var_count: u8 = 0;
    decode_one(bytes, &mut pos, &mut var_count)
}

fn varname(i: u8) -> Atom {
    Atom::sym(
        mork_expr::Expr::VARNAMES
            .get(i as usize)
            .copied()
            .unwrap_or("$z"),
    )
}

fn symbol_to_atom(s: &str) -> Atom {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if !digits.is_empty() && digits.bytes().all(|c| c.is_ascii_digit()) {
        if let Ok(n) = s.parse::<dashu::Integer>() {
            return Atom::Num(crate::atom::Numeric::Int(n));
        }
    }
    Atom::sym(s)
}

fn decode_one(b: &[u8], pos: &mut usize, var_count: &mut u8) -> Option<Atom> {
    use mork_expr::{Tag, arity_byte_count_at, byte_item, read_arity_at};
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
        Tag::LongVarRef => {
            *pos += 2;
            let i = b[*pos - 1];
            Some(varname(i))
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
    Some(Atom::Expr(crate::atom::expr_data(items)))
}

fn match_one(pattern: &Pattern, atom: &Atom) -> Option<MatchResult> {
    let mut query_bindings: Vec<(Arc<str>, Arc<Atom>)> = Vec::new();
    let mut stored_bindings: Vec<(Arc<str>, Arc<Atom>)> = Vec::new();
    if unify(pattern, atom, &mut query_bindings, &mut stored_bindings) {
        let bindings = query_bindings
            .into_iter()
            .map(|(n, v)| (n, Arc::new(substitute_stored(&*v, &stored_bindings))))
            .collect();
        Some(MatchResult {
            atom: substitute_stored(atom, &stored_bindings),
            bindings,
        })
    } else {
        None
    }
}

fn unify(
    pattern: &Pattern,
    atom: &Atom,
    query_bindings: &mut Vec<(Arc<str>, Arc<Atom>)>,
    stored_bindings: &mut Vec<(Arc<str>, Arc<Atom>)>,
) -> bool {
    if let Atom::Sym(s) = atom {
        if s.starts_with('$') && !matches!(pattern, Pattern::Any | Pattern::Var(_)) {
            let pat_atom = pattern_to_atom(pattern);
            if let Some((_, bound)) = stored_bindings
                .iter()
                .find(|(n, _)| n.as_ref() == s.as_ref())
            {
                return **bound == pat_atom;
            }
            stored_bindings.push((s.clone(), Arc::new(pat_atom)));
            return true;
        }
    }
    match pattern {
        Pattern::Any => true,
        Pattern::Var(name) => {
            if let Some((_, bound)) = query_bindings.iter().find(|(n, _)| n.as_ref() == name.as_str()) {
                **bound == *atom
            } else {
                query_bindings.push((Arc::from(name.as_str()), Arc::new(atom.clone())));
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

fn substitute_stored(atom: &Atom, bindings: &[(Arc<str>, Arc<Atom>)]) -> Atom {
    match atom {
        Atom::Sym(s) if s.starts_with('$') => bindings
            .iter()
            .find(|(name, _)| name.as_ref() == s.as_ref())
            .map(|(_, v)| (**v).clone())
            .unwrap_or_else(|| atom.clone()),
        Atom::Expr(items) => Atom::expr(
            items
                .iter()
                .map(|a| substitute_stored(a, bindings))
                .collect::<Vec<_>>(),
        ),
        _ => atom.clone(),
    }
}

fn pattern_to_atom(pattern: &Pattern) -> Atom {
    match pattern {
        Pattern::Any => Atom::sym("_"),
        Pattern::Var(name) => Atom::sym(name),
        Pattern::Exact(a) => a.clone(),
        Pattern::Expr(pats) => Atom::expr(pats.iter().map(pattern_to_atom).collect::<Vec<_>>()),
    }
}

fn atoms_equal(a: &Atom, b: &Atom) -> bool {
    match (a, b) {
        (Atom::Sym(a), Atom::Sym(b)) => a == b,
        (Atom::Num(a), Atom::Num(b)) => a == b,
        (Atom::Expr(a_items), Atom::Expr(b_items)) => {
            a_items.len() == b_items.len()
                && a_items
                    .iter()
                    .zip(b_items.iter())
                    .all(|(x, y)| atoms_equal(x, y))
        }
        _ => false,
    }
}

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
            *pos += 1;
            let mut items = Vec::new();
            loop {
                skip_whitespace(chars, pos);
                if *pos >= chars.len() {
                    return Err("unexpected end inside list".into());
                }
                if chars[*pos] == ')' {
                    *pos += 1;
                    return Ok(Atom::Expr(crate::atom::expr_data(items)));
                }
                items.push(parse_value(chars, pos)?);
            }
        }
        '"' => {
            *pos += 1;
            let mut s = String::new();
            while *pos < chars.len() && chars[*pos] != '"' {
                s.push(chars[*pos]);
                *pos += 1;
            }
            if *pos >= chars.len() {
                return Err("unterminated string".into());
            }
            *pos += 1;
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
            let n: dashu::Integer = num_str
                .parse()
                .map_err(|_| format!("invalid number: {}", num_str))?;
            Ok(Atom::Num(crate::atom::Numeric::Int(n)))
        }
        c if c.is_alphanumeric() || "$!?<>=+-*/_".contains(c) => {
            let start = *pos;
            while *pos < chars.len()
                && (chars[*pos].is_alphanumeric() || "$!?<>=+-*/_".contains(chars[*pos]))
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
