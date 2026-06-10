/// Built-in (grounded) functions: arithmetic, comparison, test.
///
/// Following maintainability rules: builtins are a single table,
/// macro-registered — one line per function.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};

macro_rules! num_binary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            let (a, b) = (expect_num(&args[0], $name, 1)?,
                          expect_num(&args[1], $name, 2)?);
            Ok(NDet::single(Atom::Num($op(a, b))))
        });
    };
}
macro_rules! cmp_binary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            expect_n_args(args, 2, $name)?;
            let (a, b) = (expect_num(&args[0], $name, 1)?,
                          expect_num(&args[1], $name, 2)?);
            Ok(NDet::single(if $op(a, b) {
                Atom::sym("True")
            } else {
                Atom::Sym(String::new())
            }))
        });
    };
}

/// Register all built-in functions into the given function table.
pub fn register_builtins(table: &mut FnTable) {
    // Arithmetic (binary, deterministic) — one line each
    num_binary!(table, "+", |a: i64, b| a + b);
    num_binary!(table, "-", |a, b| a - b);
    num_binary!(table, "*", |a, b| a * b);
    num_binary!(table, "/", |a, b| a / b);
    num_binary!(table, "%", |a, b| a % b);

    // Comparison (binary, returns True or "")
    cmp_binary!(table, "<", |a, b| a < b);
    cmp_binary!(table, ">", |a, b| a > b);
    cmp_binary!(table, "<=", |a, b| a <= b);
    cmp_binary!(table, ">=", |a, b| a >= b);

    // == compares any two atoms structurally
    table.insert_native("==", 2, |args, _| {
        expect_n_args(args, 2, "==")?;
        Ok(NDet::single(if args[0] == args[1] {
            Atom::sym("True")
        } else {
            Atom::Sym(String::new())
        }))
    });
    // Special: test (returns ok or errors)
    table.insert_native("test", 2, |args, _| {
        expect_n_args(args, 2, "test")?;
        if args[0] == args[1] {
            Ok(NDet::single(Atom::sym("ok")))
        } else {
            Err(format!(
                "test failed: expected {}, got {}",
                args[0].to_sexpr_string(),
                args[1].to_sexpr_string()
            ))
        }
    });
}

// ---- Helpers ----

fn expect_n_args(args: &[Atom], n: usize, name: &str) -> Result<(), String> {
    if args.len() != n {
        return Err(format!("{}: expected {} args, got {}", name, n, args.len()));
    }
    Ok(())
}

fn expect_num(atom: &Atom, name: &str, pos: usize) -> Result<i64, String> {
    match atom {
        Atom::Num(n) => Ok(*n),
        other => Err(format!("{}: arg {} expected number, got {}", name, pos, other.to_sexpr_string())),
    }
}
