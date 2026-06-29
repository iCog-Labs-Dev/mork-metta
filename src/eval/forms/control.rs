//! Helpers for control-oriented surface forms.

use crate::atom::Atom;
use crate::env::Env;
use crate::eval::shared::env::bind;
use crate::parser::Expr;
use std::sync::Arc;

/// Return whether an atom selects the truthy branch.
pub fn is_truthy(atom: &Atom) -> bool {
    crate::eval::shared::value::is_truthy(atom)
}

/// Extend an environment with a single binding.
pub fn bind_value(env: &Env, name: &str, value: Atom) -> Env {
    bind(env, name, value)
}

/// Return the sequential binding list for a `let*` form.
pub(crate) fn let_star_bindings(args: &[Expr]) -> Result<Arc<[Expr]>, String> {
    if args.len() != 2 {
        return Err(format!("let*: expected 2 args, got {}", args.len()));
    }
    match &args[0] {
        Expr::List(items) => Ok(Arc::clone(items)),
        _ => Err("let*: bindings must be a list".to_string()),
    }
}

/// Return one binding pair from a `let*` binding list.
pub(crate) fn let_star_binding(bindings: &[Expr], index: usize) -> Result<(&Expr, &Expr), String> {
    let pair = bindings
        .get(index)
        .ok_or_else(|| format!("let*: missing binding at index {}", index))?;
    match pair {
        Expr::List(items) if items.len() == 2 => Ok((&items[0], &items[1])),
        _ => Err("let*: each binding must be a list (pattern value)".to_string()),
    }
}
