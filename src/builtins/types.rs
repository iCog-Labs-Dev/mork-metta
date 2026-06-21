//! Builtins for structural type inspection.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};

/// Register type-inspection builtins.
pub fn register_type_builtins(funcs: &FnTable) {
    funcs.insert_native("is-var", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "is-var")?;
        let is_var = matches!(&args[0], Atom::Sym(symbol) if symbol.starts_with('$'));
        Ok(NDet::single(crate::builtins::boolean::bool_atom(is_var)))
    });
    funcs.mark_pure("is-var", 1);

    funcs.insert_native("is-expr", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "is-expr")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(matches!(
            args[0],
            Atom::Expr(_)
        ))))
    });
    funcs.mark_pure("is-expr", 1);

    funcs.insert_native("is-space", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "is-space")?;
        let is_space = matches!(&args[0], Atom::Sym(symbol) if symbol.starts_with('&'));
        Ok(NDet::single(crate::builtins::boolean::bool_atom(is_space)))
    });
    funcs.mark_pure("is-space", 1);

    funcs.insert_native("get-metatype", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "get-metatype")?;
        let kind = match &args[0] {
            Atom::Sym(symbol) if symbol.starts_with('$') => "Variable",
            Atom::Sym(_) | Atom::Num(_) | Atom::Str(_) => "Grounded",
            Atom::Expr(_) => "Expression",
            Atom::Closure(_) => "Grounded",
        };
        Ok(NDet::single(Atom::sym(kind)))
    });
    funcs.mark_pure("get-metatype", 1);

    funcs.insert_native("is-ground", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "is-ground")?;
        let is_ground = is_ground_rec(&args[0]);
        Ok(NDet::single(crate::builtins::boolean::bool_atom(is_ground)))
    });
    funcs.mark_pure("is-ground", 1);
}

fn is_ground_rec(atom: &Atom) -> bool {
    match atom {
        Atom::Sym(symbol) => !symbol.starts_with('$'),
        Atom::Expr(expr) => expr.iter().all(is_ground_rec),
        _ => true,
    }
}
