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
    Number(i128),
    /// A parenthesized list: `(fib 30)`, `(+ $N 1)`
    List(Vec<Expr>),
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
        Expr::Number(n) => Atom::Num(*n),
        Expr::List(items) => Atom::Expr(items.iter().map(expr_to_atom).collect()),
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
        Atom::Num(n) => Ok(Expr::Number(*n)),
        Atom::Expr(items) => {
            let mut exprs = Vec::with_capacity(items.len());
            for item in items {
                exprs.push(atom_to_expr(item)?);
            }
            Ok(Expr::List(exprs))
        }
        Atom::Closure(c) => {
            // Convert closure back to (|-> params body) form
            let mut items = Vec::with_capacity(3);
            items.push(Expr::Symbol("|->".to_string()));
            items.push(Expr::List(c.params.clone()));
            items.push(c.body.clone());
            Ok(Expr::List(items))
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
    let mut items = Vec::new();

    loop {
        skip_whitespace_and_comments(chars);

        match chars.peek() {
            None => return Err("unexpected end of input inside S-expression".into()),
            Some(&')') => {
                chars.next(); // consume ')'
                return Ok(Expr::List(items));
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
                if let Ok(n) = token.parse::<i128>() {
                    items.push(Expr::Number(n));
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
    let mut s = String::new();
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
