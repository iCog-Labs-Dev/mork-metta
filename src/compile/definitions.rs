//! Helpers for compiling function definitions into clause data.

use crate::func::Clause;
use crate::parser::Expr;

/// Compile a surface definition expression into a function name and clause.
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

    match &items[0] {
        Expr::Symbol(symbol) if symbol == "=" => {}
        _ => return Err("definition must start with =".into()),
    }

    let head_items = match &items[1] {
        Expr::List(items) => items,
        _ => return Err("function head must be a list (name args...)".into()),
    };

    if head_items.is_empty() {
        return Err("function head cannot be empty".into());
    }

    let name = match &head_items[0] {
        Expr::Symbol(symbol) => symbol.clone(),
        _ => return Err("function name must be a symbol".into()),
    };

    let patterns = head_items[1..].to_vec();
    let body = items[2].clone();
    Ok((name, Clause { patterns, body }))
}
