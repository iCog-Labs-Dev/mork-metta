//! Helpers for immediate surface forms.

use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;

/// Return the atom represented by a quoted expression.
pub fn quote_atom(expr: &Expr, env: &Env) -> Atom {
    crate::eval::shared::subst::subst_and_atomize(expr, env)
}

/// Return the textual representation of a surface expression.
pub fn repr_expr(expr: &Expr) -> Atom {
    Atom::sym(&expr.to_string())
}
