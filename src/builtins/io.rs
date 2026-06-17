//! Builtins for representation, parsing, assertion, and I/O.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};

/// Register representation, parsing, assertion, and I/O builtins.
pub fn register_io_builtins(funcs: &FnTable) {
    funcs.insert_native("repr", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "repr")?;
        Ok(NDet::single(Atom::str_val(&args[0].to_sexpr_string())))
    });
    funcs.mark_pure("repr", 1);

    funcs.insert_native("parse", 1, |args, _| {
        crate::builtins::arithmetic::expect_n_args(args, 1, "parse")?;
        let text = crate::eval::shared::value::expect_sym(&args[0])?;
        let expr = if let Some(rest) = text.strip_prefix('(') {
            let body = format!("({rest}");
            crate::parser::parse_sexpr_body(&mut body.chars().peekable())?
        } else {
            let forms = crate::parser::parse_forms(text)?;
            match forms.into_iter().next() {
                Some(crate::parser::TopForm::Runnable(expr)) => expr,
                Some(crate::parser::TopForm::Definition(expr)) => expr,
                None => return Err("parse: expected non-empty input".to_string()),
            }
        };
        Ok(NDet::single(crate::parser::expr_to_atom(&expr)))
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
        let input = match &args[0] {
            Atom::Sym(s) => s.to_string(),
            other => other.to_sexpr_string(),
        };
        Ok(NDet::single(sread_parse(&input)?))
    });
    funcs.mark_pure("sread", 1);
}

fn sread_parse(input: &str) -> Result<Atom, String> {
    let input = input.trim();
    if input.is_empty() {
        return Err("sread: empty input".into());
    }
    if input.starts_with('(') && input.ends_with(')') {
        let inner = input[1..input.len() - 1].trim();
        if inner.is_empty() {
            return Ok(Atom::Expr(vec![]));
        }
        let mut items = Vec::new();
        let mut depth = 0i32;
        let mut start = 0usize;
        let bytes = inner.as_bytes();
        for i in 0..bytes.len() {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                b' ' | b'\t' | b'\n' => {
                    if depth == 0 && i > start {
                        items.push(sread_parse(&inner[start..i])?);
                        start = i + 1;
                    } else if depth == 0 {
                        start = i + 1;
                    }
                }
                _ => {}
            }
        }
        if start < inner.len() {
            let token = inner[start..].trim();
            if !token.is_empty() {
                items.push(sread_parse(token)?);
            }
        }
        return Ok(Atom::Expr(items));
    }
    if let Ok(n) = input.parse::<i128>() {
        return Ok(Atom::Num(n));
    }
    Ok(Atom::sym(input))
}
