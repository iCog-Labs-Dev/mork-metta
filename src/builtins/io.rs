//! Builtins for representation, parsing, assertion, and I/O.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};
use std::sync::Arc;

/// Register representation, parsing, assertion, and I/O builtins.
pub fn register_io_builtins(funcs: &FnTable) {
    funcs.insert_native("repr", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "repr")?;
        Ok(NDet::single(Atom::str_val(&args[0].to_sexpr_string())))
    });
    funcs.mark_pure("repr", 1);

    funcs.insert_native("parse", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "parse")?;
        let text = match &args[0] {
            Atom::Sym(s) => s.as_ref(),
            Atom::Str(s) => s.as_ref(),
            other => return Err(format!("parse: expected symbol or string, got {}", other.to_sexpr_string())),
        };
        Ok(NDet::single(parse_single_expr(text)?))
    });
    funcs.mark_pure("parse", 1);

    funcs.insert_native("assert", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "assert")?;
        if crate::eval::shared::value::is_truthy(&args[0]) {
            Ok(NDet::single(Atom::sym("true")))
        } else {
            Err(format!("Assertion failed: {}", args[0].to_sexpr_string()))
        }
    });

    funcs.insert_native("test", 2, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 2, "test")?;
        if args[0] == args[1] {
            eprintln!("is {}, should {}. ✅", args[0].to_sexpr_string(), args[1].to_sexpr_string());
            Ok(NDet::single(Atom::sym("true")))
        } else {
            eprintln!("is {}, should {}. ❌", args[0].to_sexpr_string(), args[1].to_sexpr_string());
            Ok(NDet::single(Atom::sym("False")))
        }
    });
    funcs.mark_pure("test", 2);

    funcs.insert_native("sread", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "sread")?;
        let text = match &args[0] {
            Atom::Sym(s) => s.as_ref(),
            Atom::Str(s) => s.as_ref(),
            other => return Err(format!("sread: expected symbol or string, got {}", other.to_sexpr_string())),
        };
        Ok(NDet::single(parse_single_expr(text)?))
    });
    funcs.mark_pure("sread", 1);
}

// ponytail: wrap in parens to leverage parse_sexpr_body for single expression parsing
fn parse_single_expr(input: &str) -> Result<Atom, String> {
    let trimmed = input.trim();
    let body = format!("({trimmed})");
    let mut chars = body.chars().peekable();
    if chars.next() != Some('(') {
        return Err("parse: internal error".to_string());
    }
    let parsed = crate::parser::parse_sexpr_body(&mut chars)?;
    match parsed {
        crate::parser::Expr::List(items) => {
            if items.is_empty() {
                return Err("parse: expected non-empty input".to_string());
            }
            Ok(crate::parser::expr_to_atom(&items[0]))
        }
        other => Ok(crate::parser::expr_to_atom(&other)),
    }
}
