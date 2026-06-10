/// Built-in (grounded) functions: arithmetic, comparison, test, space ops.
///
/// Following maintainability rules: builtins are a single table,
/// macro-registered — one line per function.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

/// Extract a numeric value: Atom::Num(n) → n as f64, or a symbol that looks
/// like a float (e.g. "40.7") → parsed f64. Integers stay exact.
fn atom_as_f64(atom: &Atom, name: &str) -> Result<f64, String> {
    match atom {
        Atom::Num(n) => Ok(*n as f64), // SAFETY: precision loss for very large i128 but no panic
        Atom::Sym(s) => s.parse::<f64>().map_err(|_| {
            format!("{}: expected number, got {}", name, s)
        }),
        other => Err(format!("{}: expected number, got {}", name, other.to_sexpr_string())),
    }
}

/// Convert an f64 back to an Atom: whole numbers → Num(i128), fractions → Sym("n.n").
fn f64_to_atom(f: f64) -> Atom {
    if f.fract() == 0.0 && f >= i128::MIN as f64 && f <= i128::MAX as f64 {
        Atom::Num(f as i128)
    } else {
        Atom::Sym(format!("{}", f))
    }
}

macro_rules! num_binary {
    ($table:ident, $name:expr, $int_op:expr, $float_op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            // SAFETY: arity dispatch guarantees exactly 2 args reach this closure.
            Ok(NDet::single(match (&args[0], &args[1]) {
                // Both integers — stay integer (preserves truncating division etc.)
                (Atom::Num(a), Atom::Num(b)) => Atom::Num($int_op(*a, *b)),
                // At least one float-like — use float ops
                _ => {
                    let a = atom_as_f64(&args[0], $name)?;
                    let b = atom_as_f64(&args[1], $name)?;
                    f64_to_atom($float_op(a, b))
                }
            }))
        });
    };
}
macro_rules! cmp_binary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            expect_n_args(args, 2, $name)?;
            let a = atom_as_f64(&args[0], $name)?;
            let b = atom_as_f64(&args[1], $name)?;
            Ok(NDet::single(if $op(a, b) {
                Atom::sym("True")
            } else {
                Atom::Sym(String::new())
            }))
        });
    };
}

/// Register all built-in functions into the given function table.
pub fn register_builtins(table: &FnTable) {
    // Arithmetic: integer ops when both args are Num, float ops otherwise
    num_binary!(table, "+", |a: i128, b: i128| a + b, |a: f64, b: f64| a + b);
    num_binary!(table, "-", |a: i128, b: i128| a - b, |a: f64, b: f64| a - b);
    num_binary!(table, "*", |a: i128, b: i128| a * b, |a: f64, b: f64| a * b);
    num_binary!(table, "/", |a: i128, b: i128| a / b, |a: f64, b: f64| a / b);
    num_binary!(table, "%", |a: i128, b: i128| a % b, |a: f64, b: f64| a % b);

    // Comparison — use f64 so floats compare correctly
    cmp_binary!(table, "<",  |a: f64, b: f64| a < b);
    cmp_binary!(table, ">",  |a: f64, b: f64| a > b);
    cmp_binary!(table, "<=", |a: f64, b: f64| a <= b);
    cmp_binary!(table, ">=", |a: f64, b: f64| a >= b);

    // append: (append list1 list2) → concatenated list
    table.insert_native("append", 2, |args, _| {
        expect_n_args(args, 2, "append")?;
        let mut out = match &args[0] {
            Atom::Expr(items) => items.clone(),
            other => vec![other.clone()],
        };
        match &args[1] {
            Atom::Expr(items) => out.extend(items.iter().cloned()),
            other => out.push(other.clone()),
        }
        Ok(NDet::single(Atom::Expr(out)))
    });

    // == compares any two atoms structurally
    table.insert_native("==", 2, |args, _| {
        expect_n_args(args, 2, "==")?;
        Ok(NDet::single(if args[0] == args[1] {
            Atom::sym("True")
        } else {
            Atom::Sym(String::new())
        }))
    });

    // test: (test actual expected) — compares two atoms, errors on mismatch
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


    // add-atom: (add-atom &space atom)
    // PeTTa semantics: if the atom is a (= head body) definition, also registers
    // the function so subsequent expressions can call it.
    table.insert_native("add-atom", 2, |args, table| {
        expect_n_args(args, 2, "add-atom")?;
        let atom = &args[1];
        table.space.borrow_mut().add_atom(atom).map_err(|e| format!("add-atom: {}", e))?;
        // If the atom is a function definition (= head body), register it
        if let Atom::Expr(items) = atom {
            if items.len() == 3 && items[0] == Atom::sym("=") {
                if let (Ok(head_expr), Ok(body_expr)) = (
                    crate::parser::atom_to_expr(&items[1]),
                    crate::parser::atom_to_expr(&items[2]),
                ) {
                    let def_expr = Expr::List(vec![
                        Expr::Symbol("=".to_string()),
                        head_expr,
                        body_expr,
                    ]);
                    if let Ok((name, clause)) = crate::compile::compile_definition(&def_expr) {
                        table.add_clause(name, clause.patterns, clause.body);
                    }
                }
            }
        }
        Ok(NDet::single(Atom::sym("true")))
    });

    // remove-atom: (remove-atom &space atom) — removes an atom, returns true/false
    table.insert_native("remove-atom", 2, |args, table| {
        expect_n_args(args, 2, "remove-atom")?;
        let atom = &args[1];
        let removed = table.space.borrow_mut().remove_atom(atom)
            .map_err(|e| format!("remove-atom: {}", e))?;
        // Keep FnTable in sync: if removed atom was a function definition, drop its clause.
        if removed {
            if let Atom::Expr(items) = atom {
                if items.len() == 3 && items[0] == Atom::sym("=") {
                    if let (Ok(head_expr), Ok(body_expr)) = (
                        crate::parser::atom_to_expr(&items[1]),
                        crate::parser::atom_to_expr(&items[2]),
                    ) {
                        let def_expr = Expr::List(vec![
                            Expr::Symbol("=".to_string()),
                            head_expr,
                            body_expr,
                        ]);
                        if let Ok((name, clause)) = crate::compile::compile_definition(&def_expr) {
                            table.remove_clause(&name, &clause.patterns, &clause.body);
                        }
                    }
                }
            }
        }
        Ok(NDet::single(if removed {
            Atom::sym("true")
        } else {
            Atom::Sym(String::new()) // false/empty
        }))
    });

    // repr: (repr atom) — return the S-expression string of an atom as a symbol
    table.insert_native("repr", 1, |args, _| {
        expect_n_args(args, 1, "repr")?;
        Ok(NDet::single(Atom::sym(&args[0].to_sexpr_string())))
    });

    // get-state: (get-state key) — retrieves state value
    table.insert_native("get-state", 1, |args, table| {
        expect_n_args(args, 1, "get-state")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.clone(),
            other => return Err(format!("get-state: key must be a symbol, got {}", other.to_sexpr_string())),
        };
        let state = table.state.borrow();
        match state.get(&key) {
            Some(val) => Ok(NDet::single(val.clone())),
            None => Err(format!("get-state: no value for key '{}'", key)),
        }
    });

    // change-state!: (change-state! key value) — stores state, returns true
    table.insert_native("change-state!", 2, |args, table| {
        expect_n_args(args, 2, "change-state!")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.clone(),
            other => return Err(format!("change-state!: key must be a symbol, got {}", other.to_sexpr_string())),
        };
        table.state.borrow_mut().insert(key, args[1].clone());
        Ok(NDet::single(Atom::sym("true")))
    });

    // bind!: (bind! name (new-state value)) — destructures new-state wrapper,
    // then stores. Also handles (bind! name value) for direct assignment.
    table.insert_native("bind!", 2, |args, table| {
        expect_n_args(args, 2, "bind!")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.clone(),
            other => return Err(format!("bind!: key must be a symbol, got {}", other.to_sexpr_string())),
        };
        // PeTTa semantics: destructure (new-state value) wrapper
        let value = match &args[1] {
            Atom::Expr(items) if items.len() == 2 && items[0] == Atom::sym("new-state") => {
                items[1].clone()
            }
            other => other.clone(),
        };
        table.state.borrow_mut().insert(key, value);
        Ok(NDet::single(Atom::sym("true")))
    });

    // cons-atom: (cons-atom elem list) → prepend elem to list
    table.insert_native("cons-atom", 2, |args, _| {
        expect_n_args(args, 2, "cons-atom")?;
        let mut out = vec![args[0].clone()];
        match &args[1] {
            Atom::Expr(items) => out.extend(items.iter().cloned()),
            other => out.push(other.clone()),
        }
        Ok(NDet::single(Atom::Expr(out)))
    });

    // car-atom: (car-atom list) → first element
    table.insert_native("car-atom", 1, |args, _| {
        expect_n_args(args, 1, "car-atom")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("car-atom: empty list".into()),
            other => Err(format!("car-atom: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // cdr-atom: (cdr-atom list) → tail (all but first)
    table.insert_native("cdr-atom", 1, |args, _| {
        expect_n_args(args, 1, "cdr-atom")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => {
                Ok(NDet::single(Atom::Expr(items[1..].to_vec())))
            }
            Atom::Expr(_) => Err("cdr-atom: empty list".into()),
            other => Err(format!("cdr-atom: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // index-atom: (index-atom list n) → 0-based nth element
    table.insert_native("index-atom", 2, |args, _| {
        expect_n_args(args, 2, "index-atom")?;
        let idx = match &args[1] {
            Atom::Num(n) => usize::try_from(*n)
                .map_err(|_| format!("index-atom: index must be non-negative, got {}", n))?,
            other => return Err(format!("index-atom: index must be a number, got {}", other.to_sexpr_string())),
        };
        match &args[0] {
            Atom::Expr(items) => items.get(idx)
                .cloned()
                .map(NDet::single)
                .ok_or_else(|| format!("index-atom: index {} out of bounds (len {})", idx, items.len())),
            other => Err(format!("index-atom: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // id: (id x) → x
    table.insert_native("id", 1, |args, _| {
        expect_n_args(args, 1, "id")?;
        Ok(NDet::single(args[0].clone()))
    });

    // =alpha: (=alpha expr1 expr2) → True/False — structural equality up to variable renaming
    table.insert_native("=alpha", 2, |args, _| {
        expect_n_args(args, 2, "=alpha")?;
        let mut map_ab = std::collections::HashMap::new();
        let mut map_ba = std::collections::HashMap::new();
        let eq = alpha_equiv(&args[0], &args[1], &mut map_ab, &mut map_ba);
        Ok(NDet::single(if eq { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // first-from-pair: (first-from-pair (A B)) → A
    table.insert_native("first-from-pair", 1, |args, _| {
        expect_n_args(args, 1, "first-from-pair")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("first-from-pair: empty list".into()),
            other => Err(format!("first-from-pair: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // second-from-pair: (second-from-pair (A B)) → B
    table.insert_native("second-from-pair", 1, |args, _| {
        expect_n_args(args, 1, "second-from-pair")?;
        match &args[0] {
            Atom::Expr(items) if items.len() >= 2 => Ok(NDet::single(items[1].clone())),
            Atom::Expr(_) => Err("second-from-pair: list too short".into()),
            other => Err(format!("second-from-pair: expected list, got {}", other.to_sexpr_string())),
        }
    });
}

// ---- Helpers ----

fn alpha_equiv(
    a: &Atom,
    b: &Atom,
    map_ab: &mut std::collections::HashMap<String, String>,
    map_ba: &mut std::collections::HashMap<String, String>,
) -> bool {
    match (a, b) {
        (Atom::Sym(sa), Atom::Sym(sb)) => {
            let a_var = sa.starts_with('$');
            let b_var = sb.starts_with('$');
            match (a_var, b_var) {
                (true, true) => {
                    let fwd = map_ab.entry(sa.clone()).or_insert_with(|| sb.clone());
                    let fwd_ok = fwd.as_str() == sb.as_str();
                    let bwd = map_ba.entry(sb.clone()).or_insert_with(|| sa.clone());
                    fwd_ok && bwd.as_str() == sa.as_str()
                }
                (false, false) => sa == sb,
                _ => false,
            }
        }
        (Atom::Num(a), Atom::Num(b)) => a == b,
        (Atom::Expr(as_), Atom::Expr(bs)) => {
            as_.len() == bs.len()
                && as_.iter().zip(bs.iter()).all(|(x, y)| alpha_equiv(x, y, map_ab, map_ba))
        }
        _ => false,
    }
}

fn expect_n_args(args: &[Atom], n: usize, name: &str) -> Result<(), String> {
    if args.len() != n {
        return Err(format!("{}: expected {} args, got {}", name, n, args.len()));
    }
    Ok(())
}

