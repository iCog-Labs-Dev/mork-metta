//! Helpers for converting between parsed expressions and runtime atoms.

use crate::atom::Atom;
use crate::parser::Expr;
use std::sync::Arc;

/// Convert a parsed expression into a runtime atom.
pub fn expr_to_atom(expr: &Expr) -> Atom {
    match expr {
        Expr::Symbol(symbol) => Atom::sym(symbol),
        Expr::Str(s) => Atom::str_val(s),
        Expr::Number(number) => Atom::Num(number.clone()),
        Expr::List(items) => Atom::expr(items.iter().map(expr_to_atom).collect::<Vec<_>>()),
    }
}

/// Convert a runtime atom into a parsed expression.
pub fn atom_to_expr(atom: &Atom) -> Result<Expr, String> {
    match atom {
        Atom::Sym(symbol) => Ok(Expr::Symbol(symbol.to_string())),
        Atom::Str(s) => Ok(Expr::Str(s.to_string())),
        Atom::Num(number) => Ok(Expr::Number(number.clone())),
        Atom::Expr(items) => {
            let mut exprs = Vec::with_capacity(items.len());
            for item in items.iter() {
                exprs.push(atom_to_expr(item)?);
            }
            Ok(Expr::List(exprs.into()))
        }
        Atom::Closure(closure) => {
            let items: Vec<Expr> = vec![
                Expr::Symbol("|->".to_string()),
                Expr::List(Arc::from(closure.params.as_slice())),
                closure.body.clone(),
            ];
            Ok(Expr::List(items.into()))
        }
        Atom::Gnd(g) => {
            Ok(Expr::Symbol(g.display_metta()))
        }
    }
}
