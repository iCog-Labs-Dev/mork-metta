/// S-expression parser for a minimal MeTTa subset.
///
/// Handles:
/// - `;` comments (to end of line)
/// - Nested `(...)` S-expressions
/// - Integer tokens (`123`, `-42`)
/// - Symbol tokens (`fib`, `$N`, `+`, `if`, `test`, `=`)
/// - Top-level forms:
///   - `(= (head ...) body)` → `TopForm::Definition`
///   - `!( ... )` → `TopForm::Runnable`
///
/// No string literals, no quoting, no dotted pairs.
///
/// # Assumptions
/// - All tokens are whitespace-delimited; no delimiters inside tokens.
/// - Comments begin with `;` and extend to end of line.
/// - Integer tokens are prefixed or unprefixed ASCII digits.
/// - Symbols can contain any non-whitespace, non-paren characters.
use crate::atom::Atom;
use std::sync::Arc;

/// A top-level form in a MeTTa file.
#[derive(Clone, Debug)]
pub enum TopForm {
    /// A function definition: `(= (head ...) body)`
    Definition(Expr),
    /// A runnable expression: `!(expr)`
    Runnable(Expr),
}

/// A parsed but not-yet-compiled MeTTa expression.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A symbolic token: `fib`, `$N`, `+`, `if`, `=`
    Symbol(String),
    /// A string literal: `"hello"`, `"foo bar"`
    Str(String),
    /// An integer literal: `30`, `-1`, `354224848179261915075`
    Number(crate::atom::Numeric),
    /// A parenthesized list: `(fib 30)`, `(+ $N 1)`
    List(Arc<[Expr]>),
}

impl Expr {
    /// Convert an `Expr` back to a display string (for error messages).
    pub fn to_string(&self) -> String {
        match self {
            Expr::Symbol(s) => s.clone(),
            Expr::Str(s) => {
                let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
                format!("\"{}\"", escaped)
            }
            Expr::Number(n) => n.to_string(),
            Expr::List(items) => {
                let inner: Vec<String> = items.iter().map(|e| e.to_string()).collect();
                format!("({})", inner.join(" "))
            }
        }
    }
}

/// Convert a parsed `Expr` tree to an `Atom` data value (no evaluation).
///
/// This is the inverse of `atom_to_expr`. Used by `quote` to return
/// unevaluated expression trees as data, and by `lib.rs` for space storage.
///
/// # Assumptions
/// - Every Expr has a corresponding Atom representation.
/// - The conversion is lossless: `atom_to_expr(expr_to_atom(e)) == Ok(e)`.
pub fn expr_to_atom(expr: &Expr) -> Atom {
    match expr {
        Expr::Symbol(s) => Atom::sym(s),
        Expr::Str(s) => Atom::str_val(s),
        Expr::Number(n) => Atom::Num(n.clone()),
        Expr::List(items) => Atom::expr(items.iter().map(expr_to_atom).collect::<Vec<_>>()),
    }
}

/// Convert a stored `Atom` back to an `Expr` for evaluation.
///
/// This is the inverse of `expr_to_atom`. Used by `eval` special form to
/// interpret data atoms as runnable code, and by `lib.rs` for reification.
///
/// # Errors
/// Returns an error if the atom cannot be represented as an Expr
/// (currently all Atom variants map cleanly, so this never fails in practice).
///
/// # Assumptions
/// - Every Atom has a corresponding Expr representation.
/// - The conversion is lossless: `expr_to_atom(&atom_to_expr(a)?) == a`.
pub fn atom_to_expr(atom: &Atom) -> Result<Expr, String> {
    match atom {
        Atom::Sym(s) => Ok(Expr::Symbol(s.to_string())),
        Atom::Str(s) => Ok(Expr::Str(s.to_string())),
        Atom::Num(n) => Ok(Expr::Number(n.clone())),
        Atom::Expr(items) => {
            let mut exprs = Vec::with_capacity(items.len());
            for item in items.iter() {
                exprs.push(atom_to_expr(item)?);
            }
            Ok(Expr::List(exprs.into()))
        }
        Atom::Closure(c) => {
            // Convert closure back to (|-> params body) form
            let items: Vec<Expr> = vec![
                Expr::Symbol("|->".to_string()),
                Expr::List(Arc::from(c.params.as_slice())),
                c.body.clone(),
            ];
            Ok(Expr::List(items.into()))
        }
    }
}

/// Parse a full MeTTa source string into a list of top-level forms.
///
/// Strips comments, splits into balanced `(...)` or `!(...)` blocks,
/// then parses each block as an S-expression.
///
/// # Assumptions
/// - Forms are delimited by balanced parentheses.
/// - `!(...)` prefix marks a runnable form.
/// - Anything without `!` prefix is treated as a definition form.
pub fn parse_forms(input: &str) -> Result<Vec<TopForm>, String> {
    let mut chars = input.chars().peekable();
    let mut forms = Vec::new();

    loop {
        // Skip whitespace and comments
        skip_whitespace_and_comments(&mut chars);
        if chars.peek().is_none() {
            break;
        }

        // Check for runnable prefix `!(`
        let is_runnable = if let Some(&'!') = chars.peek() {
            chars.next(); // consume '!'
            true
        } else {
            false
        };

        // Must start with '('
        match chars.next() {
            Some('(') => {}
            Some(c) => return Err(format!("expected '(' at start of form, found '{}'", c)),
            None => return Err("unexpected end of input".into()),
        }

        // Read balanced sexpr
        let expr = parse_sexpr_body(&mut chars)?;

        if is_runnable {
            forms.push(TopForm::Runnable(expr));
        } else {
            forms.push(TopForm::Definition(expr));
        }
    }

    Ok(forms)
}

/// Parse a single S-expression from a character stream.
/// Assumes the opening '(' has already been consumed.
pub(crate) fn parse_sexpr_body(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<Expr, String> {
    let mut items = Vec::with_capacity(4);

    loop {
        skip_whitespace_and_comments(chars);

        match chars.peek() {
            None => return Err("unexpected end of input inside S-expression".into()),
            Some(&')') => {
                chars.next(); // consume ')'
                return Ok(Expr::List(items.into()));
            }
            Some(&'(') => {
                chars.next(); // consume '('
                let sub = parse_sexpr_body(chars)?;
                items.push(sub);
            }
            Some(&'"') => {
                let token = read_token(chars);
                items.push(Expr::Str(token));
            }
            Some(&_) => {
                let token = read_token(chars);
                // Pure integer: only digits (with optional leading '-').
                // Dashu accepts '_' separators so we guard manually to keep
                // atoms like 2025_12_12 as symbols, not numbers.
                let pure_int = {
                    let s = token.trim_start_matches('-');
                    !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit())
                };
                if pure_int {
                    if let Ok(n) = token.parse::<dashu::Integer>() {
                        items.push(Expr::Number(crate::atom::Numeric::Int(n)));
                    } else {
                        items.push(Expr::Symbol(token));
                    }
                } else if token.contains('.') || token.contains('e') || token.contains('E') {
                    match token.parse::<dashu::Decimal>() {
                        Ok(n) => items.push(Expr::Number(crate::atom::Numeric::Dec(n))),
                        Err(_) => items.push(Expr::Symbol(token)),
                    }
                } else {
                    items.push(Expr::Symbol(token));
                }
            }
        }
    }
}

/// Read a token (whitespace-delimited, also stops at '(' and ')').
/// If the token starts with `"`, read until the closing `"` and return
/// the content between quotes as a single token (parens inside are literal).
fn read_token(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> String {
    let mut s = String::with_capacity(32);
    // Quoted string: read until closing "
    if let Some(&'"') = chars.peek() {
        chars.next(); // consume opening "
        while let Some(&c) = chars.peek() {
            if c == '"' {
                chars.next();
                break;
            }
            if c == '\\' {
                chars.next();
                if let Some(&esc) = chars.peek() {
                    chars.next();
                    match esc {
                        '"' => s.push('"'),
                        '\\' => s.push('\\'),
                        'n' => s.push('\n'),
                        't' => s.push('\t'),
                        other => { s.push('\\'); s.push(other); }
                    }
                }
                continue;
            }
            s.push(c);
            chars.next();
        }
        return s;
    }
    // Normal token: whitespace/paren delimited
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == '(' || c == ')' {
            break;
        }
        s.push(c);
        chars.next();
    }
    s
}

/// Skip whitespace and `;` comments.
fn skip_whitespace_and_comments(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    loop {
        // Skip whitespace
        while let Some(&c) = chars.peek() {
            if c.is_whitespace() {
                chars.next();
            } else {
                break;
            }
        }
        // Skip comment line
        if let Some(&';') = chars.peek() {
            chars.next(); // consume ';'
            while let Some(&c) = chars.peek() {
                if c == '\n' {
                    break;
                }
                chars.next();
            }
        } else {
            break;
        }
    }
}

/// Parse a `(...)` form from `content` starting at `pos` (which must point at `(`),
/// producing an `Atom` directly — no `Expr` intermediate, no per-token String allocation.
/// Tokens are borrowed as `&str` slices from `content`; only numeric literals and
/// string escapes require heap allocation.
/// Advances `pos` past the closing `)`.
pub fn parse_atom_bytes(
    content: &str,
    pos: &mut usize,
    line_no: &mut usize,
) -> Result<Atom, String> {
    let bytes = content.as_bytes();
    debug_assert_eq!(bytes.get(*pos), Some(&b'('), "parse_atom_bytes must start at '('");
    *pos += 1; // consume '('
    let mut items: Vec<Atom> = Vec::with_capacity(4);

    loop {
        // skip whitespace and ; comments
        loop {
            while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
                if bytes[*pos] == b'\n' {
                    *line_no += 1;
                }
                *pos += 1;
            }
            if *pos < bytes.len() && bytes[*pos] == b';' {
                while *pos < bytes.len() && bytes[*pos] != b'\n' {
                    *pos += 1;
                }
            } else {
                break;
            }
        }

        if *pos >= bytes.len() {
            return Err("unexpected end of input inside S-expression".into());
        }

        match bytes[*pos] {
            b')' => {
                *pos += 1;
                return Ok(Atom::Expr(crate::atom::expr_data(items)));
            }
            b'(' => {
                items.push(parse_atom_bytes(content, pos, line_no)?);
            }
            b'"' => {
                *pos += 1; // consume opening '"'
                let mut s = String::new();
                while *pos < bytes.len() {
                    match bytes[*pos] {
                        b'\\' if *pos + 1 < bytes.len() => {
                            *pos += 1;
                            let esc = bytes[*pos];
                            *pos += 1;
                            match esc {
                                b'"' => s.push('"'),
                                b'\\' => s.push('\\'),
                                b'n' => s.push('\n'),
                                b't' => s.push('\t'),
                                c => {
                                    s.push('\\');
                                    s.push(c as char);
                                }
                            }
                        }
                        b'"' => {
                            *pos += 1;
                            break;
                        }
                        b'\n' => {
                            *line_no += 1;
                            s.push('\n');
                            *pos += 1;
                        }
                        _ => {
                            // Handle multi-byte UTF-8 inside strings
                            let ch = content[*pos..].chars().next().unwrap();
                            s.push(ch);
                            *pos += ch.len_utf8();
                        }
                    }
                }
                items.push(Atom::str_val(s.as_str()));
            }
            _ => {
                // Symbol or number: zero-copy slice until delimiter
                let start = *pos;
                while *pos < bytes.len() {
                    let b = bytes[*pos];
                    if b.is_ascii_whitespace() || b == b'(' || b == b')' || b == b';' {
                        break;
                    }
                    *pos += 1;
                }
                items.push(bytes_token_to_atom(&content[start..*pos]));
            }
        }
    }
}

fn bytes_token_to_atom(token: &str) -> Atom {
    let s = token.trim_start_matches('-');
    if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) {
        if let Ok(n) = token.parse::<dashu::Integer>() {
            return Atom::Num(crate::atom::Numeric::Int(n));
        }
    } else if token.contains('.') || token.contains('e') || token.contains('E') {
        if let Ok(n) = token.parse::<dashu::Decimal>() {
            return Atom::Num(crate::atom::Numeric::Dec(n));
        }
    }
    Atom::sym(token)
}
