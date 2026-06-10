/// Compiler: converts a parsed `(= (name args...) body)` form into a `Clause`.
///
/// The compiler does minimal work — it extracts the function name and stores
/// the raw pattern expressions and body for the evaluator to dispatch on.

use crate::func::Clause;
use crate::parser::Expr;

/// Try to parse an expression as a user-defined function clause.
///
/// Expects shape:
/// ```metta
/// List([Symbol("="), List([Symbol(name), pattern1, pattern2, ...]), body])
/// ```
///
/// Returns `(name, Clause)` on success. `Clause.patterns` contains the raw
/// pattern expressions — these can be `$var` (variable), literal symbols,
/// literal numbers, or nested lists (structural patterns).
///
/// # Errors
/// - If the shape doesn't match: not a list, not 3 elements, doesn't start with `=`
/// - If the head isn't a list starting with a non-variable symbol
pub fn compile_definition(expr: &Expr) -> Result<(String, Clause), String> {
    let items = match expr {
        Expr::List(items) => items,
        _ => return Err("definition must be a list".into()),
    };

    if items.len() != 3 {
        return Err(format!(
            "definition expects 3 elements (= head body), got {}",
            items.len()
        ));
    }

    // First element must be Symbol("=")
    match &items[0] {
        Expr::Symbol(s) if s == "=" => {}
        _ => return Err("definition must start with =".into()),
    }

    // Second element must be a list: (name patterns...)
    let head_items = match &items[1] {
        Expr::List(v) => v,
        _ => return Err("function head must be a list (name args...)".into()),
    };

    if head_items.is_empty() {
        return Err("function head cannot be empty".into());
    }

    // First element of head is the function name
    let name = match &head_items[0] {
        Expr::Symbol(s) => {
            if s.starts_with('$') {
                return Err(format!("function name cannot be a variable: {}", s));
            }
            s.clone()
        }
        _ => return Err("function name must be a symbol".into()),
    };

    // Remaining elements are pattern expressions — can be $var, literals,
    // numbers, or nested lists. Accept any Expr.
    let patterns: Vec<Expr> = head_items[1..].to_vec();

    // Third element is the body
    let body = items[2].clone();

    Ok((name, Clause { patterns, body }))
}
