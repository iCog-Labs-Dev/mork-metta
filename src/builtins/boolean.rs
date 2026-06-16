//! Builtins for boolean values, logical operators, and equality comparisons.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

/// Convert a Rust boolean into a MeTTa boolean atom.
pub fn bool_atom(value: bool) -> Atom {
    if value {
        Atom::sym("True")
    } else {
        Atom::sym("False")
    }
}

/// Register boolean and equality builtins.
pub fn register_boolean_builtins(funcs: &FnTable) {
    // Truth table clauses via space (constraint eval threads bindings through them)
    register_truth_tables(funcs);

    funcs.insert_native("==", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "==")?;
        Ok(NDet::single(bool_atom(args[0] == args[1])))
    });
    funcs.mark_pure("==", 2);

    funcs.insert_native("!=", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "!=")?;
        Ok(NDet::single(bool_atom(args[0] != args[1])))
    });
    funcs.mark_pure("!=", 2);

    funcs.insert_native("=", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "=")?;
        Ok(NDet::single(bool_atom(args[0] == args[1])))
    });
    funcs.mark_pure("=", 2);

    funcs.insert_native("=?", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "=?")?;
        Ok(NDet::single(bool_atom(args[0] == args[1])))
    });
    funcs.mark_pure("=?", 2);

    funcs.insert_native("same", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "same")?;
        Ok(NDet::single(bool_atom(args[0] == args[1])))
    });
    funcs.mark_pure("same", 2);

    funcs.insert_native("=alpha", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "=alpha")?;
        let mut map_ab = std::collections::HashMap::new();
        let mut map_ba = std::collections::HashMap::new();
        let eq = crate::builtins::arithmetic::alpha_equiv(
            &args[0],
            &args[1],
            &mut map_ab,
            &mut map_ba,
        );
        Ok(NDet::single(bool_atom(eq)))
    });
    funcs.mark_pure("=alpha", 2);
}

fn register_truth_tables(funcs: &FnTable) {
    let clauses: &[(&str, &[&str], &str)] = &[
        ("or", &["True", "True"], "True"),
        ("or", &["True", "False"], "True"),
        ("or", &["False", "True"], "True"),
        ("or", &["False", "False"], "False"),
        ("and", &["True", "True"], "True"),
        ("and", &["True", "False"], "False"),
        ("and", &["False", "True"], "False"),
        ("and", &["False", "False"], "False"),
        ("not", &["True"], "False"),
        ("not", &["False"], "True"),
        ("xor", &["True", "False"], "True"),
        ("xor", &["False", "True"], "True"),
        ("xor", &["True", "True"], "False"),
        ("xor", &["False", "False"], "False"),
        ("implies", &["True", "True"], "True"),
        ("implies", &["True", "False"], "False"),
        ("implies", &["False", "True"], "True"),
        ("implies", &["False", "False"], "True"),
    ];

    for &(name, patterns, body_str) in clauses {
        let head = Expr::List(
            std::iter::once(Expr::Symbol(name.to_string()))
                .chain(patterns.iter().map(|p| Expr::Symbol(p.to_string())))
                .collect(),
        );
        let body = Expr::Symbol(body_str.to_string());
        let def_expr = Expr::List(vec![
            Expr::Symbol("=".to_string()),
            head.clone(),
            body,
        ]);
        let def_atom = crate::parser::expr_to_atom(&def_expr);
        funcs.space.write().unwrap().add_atom(&def_atom).unwrap();
        let head_atom = crate::parser::expr_to_atom(&head);
        funcs.space.write().unwrap().add_atom(&head_atom).unwrap();
        let clause = crate::func::Clause {
            patterns: patterns.iter().map(|p| Expr::Symbol(p.to_string())).collect(),
            body: Expr::Symbol(body_str.to_string()),
        };
        let arity = clause.patterns.len() as u8;
        funcs.cache_fn(name, arity, clause);
    }

    // mark pure
    for (name, arity) in [("or", 2u8), ("and", 2), ("not", 1), ("xor", 2), ("implies", 2)] {
        funcs.mark_pure(name, arity);
    }
}
