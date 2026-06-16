//! Helpers for converting between parsed expressions and runtime atoms.

use crate::atom::Atom;
use crate::parser::Expr;

/// Convert a parsed expression into a runtime atom.
pub fn expr_to_atom(expr: &Expr) -> Atom {
    match expr {
        Expr::Symbol(symbol) => Atom::sym(symbol),
        Expr::Number(number) => Atom::Num(*number),
        Expr::List(items) => Atom::Expr(items.iter().map(expr_to_atom).collect()),
    }
}

/// Convert a runtime atom into a parsed expression.
pub fn atom_to_expr(atom: &Atom) -> Result<Expr, String> {
    match atom {
        Atom::Sym(symbol) => Ok(Expr::Symbol(symbol.to_string())),
        Atom::Num(number) => Ok(Expr::Number(*number)),
        Atom::Expr(items) => {
            let mut exprs = Vec::with_capacity(items.len());
            for item in items {
                exprs.push(atom_to_expr(item)?);
            }
            Ok(Expr::List(exprs))
        }
        Atom::Closure(closure) => Ok(Expr::List(vec![
            Expr::Symbol("|->".to_string()),
            Expr::List(closure.params.clone()),
            closure.body.clone(),
        ])),
    }
}
