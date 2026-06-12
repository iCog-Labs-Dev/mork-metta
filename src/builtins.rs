/// Built-in (grounded) functions: arithmetic, comparison, test, space ops.
///
/// Following maintainability rules: builtins are a single table,
/// macro-registered — one line per function.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

macro_rules! bool_clause {
    ($table:ident, $name:expr, [$($p:expr),+], $body:expr) => {
        $table.add_clause(
            $name.to_string(),
            vec![$( Expr::Symbol($p.to_string()) ),+],
            Expr::Symbol($body.to_string()),
        );
    };
}

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
        Atom::sym(&f.to_string())
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
                Atom::sym("False")
            }))
        });
    };
}

macro_rules! math_unary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 1, |args, _| {
            let x = atom_as_f64(&args[0], $name)?;
            Ok(NDet::single(f64_to_atom($op(x))))
        });
    };
}

macro_rules! math_binary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            let a = atom_as_f64(&args[0], $name)?;
            let b = atom_as_f64(&args[1], $name)?;
            Ok(NDet::single(f64_to_atom($op(a, b))))
        });
    };
}

/// Register all built-in functions into the given function table.
pub fn register_builtins(table: &FnTable) {
    // Boolean truth tables (user-defined clauses so constraint eval threads bindings)
    bool_clause!(table, "or",  ["True",  "True"],  "True");
    bool_clause!(table, "or",  ["True",  "False"], "True");
    bool_clause!(table, "or",  ["False", "True"],  "True");
    bool_clause!(table, "or",  ["False", "False"], "False");
    bool_clause!(table, "and", ["True",  "True"],  "True");
    bool_clause!(table, "and", ["True",  "False"], "False");
    bool_clause!(table, "and", ["False", "True"],  "False");
    bool_clause!(table, "and", ["False", "False"], "False");
    bool_clause!(table, "not", ["True"],           "False");
    bool_clause!(table, "not", ["False"],          "True");

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

    // != (negated structural equality)
    table.insert_native("!=", 2, |args, _| {
        Ok(NDet::single(if args[0] != args[1] { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // xor truth table (user-defined so constraint eval threads bindings)
    bool_clause!(table, "xor", ["True",  "False"], "True");
    bool_clause!(table, "xor", ["False", "True"],  "True");
    bool_clause!(table, "xor", ["True",  "True"],  "False");
    bool_clause!(table, "xor", ["False", "False"], "False");

    // Float unary math — (fn-math x)
    math_unary!(table, "sqrt-math",  |x: f64| x.sqrt());
    math_unary!(table, "abs-math",   |x: f64| x.abs());
    math_unary!(table, "trunc-math", |x: f64| x.trunc());
    math_unary!(table, "ceil-math",  |x: f64| x.ceil());
    math_unary!(table, "floor-math", |x: f64| x.floor());
    math_unary!(table, "round-math", |x: f64| x.round());
    math_unary!(table, "sin-math",   |x: f64| x.sin());
    math_unary!(table, "asin-math",  |x: f64| x.asin());
    math_unary!(table, "cos-math",   |x: f64| x.cos());
    math_unary!(table, "acos-math",  |x: f64| x.acos());
    math_unary!(table, "tan-math",   |x: f64| x.tan());
    math_unary!(table, "atan-math",  |x: f64| x.atan());
    math_unary!(table, "exp",        |x: f64| x.exp());

    // Float binary math
    math_binary!(table, "pow-math", |a: f64, b: f64| a.powf(b));
    math_binary!(table, "log-math", |a: f64, b: f64| a.log(b));
    math_binary!(table, "min",      |a: f64, b: f64| a.min(b));
    math_binary!(table, "max",      |a: f64, b: f64| a.max(b));

    // isnan-math / isinf-math predicates
    table.insert_native("isnan-math", 1, |args, _| {
        let x = atom_as_f64(&args[0], "isnan-math")?;
        Ok(NDet::single(if x.is_nan() { Atom::sym("True") } else { Atom::sym("False") }))
    });
    table.insert_native("isinf-math", 1, |args, _| {
        let x = atom_as_f64(&args[0], "isinf-math")?;
        Ok(NDet::single(if x.is_infinite() { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // min-atom / max-atom: (min-atom (list...)) → Number
    table.insert_native("min-atom", 1, |args, _| {
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut best = f64::INFINITY;
        for item in &items {
            best = best.min(atom_as_f64(item, "min-atom")?);
        }
        Ok(NDet::single(f64_to_atom(best)))
    });
    table.insert_native("max-atom", 1, |args, _| {
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut best = f64::NEG_INFINITY;
        for item in &items {
            best = best.max(atom_as_f64(item, "max-atom")?);
        }
        Ok(NDet::single(f64_to_atom(best)))
    });

    // size-atom: (size-atom list) → Number
    table.insert_native("size-atom", 1, |args, _| {
        expect_n_args(args, 1, "size-atom")?;
        let len = match &args[0] {
            Atom::Expr(items) => items.len(),
            _ => 1,
        };
        Ok(NDet::single(Atom::Num(len as i128)))
    });

    // length: (length list) → Number — alias for size-atom
    table.insert_native("length", 1, |args, _| {
        expect_n_args(args, 1, "length")?;
        let len = match &args[0] {
            Atom::Expr(items) => items.len(),
            _ => 1,
        };
        Ok(NDet::single(Atom::Num(len as i128)))
    });

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

    // msort: (msort list) → sorted list (keeps duplicates)
    table.insert_native("msort", 1, |args, _| {
        expect_n_args(args, 1, "msort")?;
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut sorted = items;
        sorted.sort_by(|a, b| {
            a.to_sexpr_string().cmp(&b.to_sexpr_string())
        });
        Ok(NDet::single(Atom::Expr(sorted)))
    });

    // sort: (sort list) → sorted deduplicated list
    table.insert_native("sort", 1, |args, _| {
        expect_n_args(args, 1, "sort")?;
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut sorted = items;
        sorted.sort_by(|a, b| {
            a.to_sexpr_string().cmp(&b.to_sexpr_string())
        });
        sorted.dedup();
        Ok(NDet::single(Atom::Expr(sorted)))
    });

    // == compares any two atoms structurally
    table.insert_native("==", 2, |args, _| {
        expect_n_args(args, 2, "==")?;
        Ok(NDet::single(if args[0] == args[1] {
            Atom::sym("True")
        } else {
            Atom::sym("False")
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


    // repr: (repr atom) — return the S-expression string of an atom as a symbol
    table.insert_native("repr", 1, |args, _| {
        expect_n_args(args, 1, "repr")?;
        Ok(NDet::single(Atom::sym(&args[0].to_sexpr_string())))
    });

    // get-state: (get-state key) — retrieves state value
    table.insert_native("get-state", 1, |args, table| {
        expect_n_args(args, 1, "get-state")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.to_string(),
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
            Atom::Sym(s) => s.to_string(),
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
            Atom::Sym(s) => s.to_string(),
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

    // cons: (cons elem list) → prepend elem to list — alias for cons-atom
    table.insert_native("cons", 2, |args, _| {
        expect_n_args(args, 2, "cons")?;
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

    // car: (car list) → first element — alias for car-atom
    table.insert_native("car", 1, |args, _| {
        expect_n_args(args, 1, "car")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("car: empty list".into()),
            other => Err(format!("car: expected list, got {}", other.to_sexpr_string())),
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

    // cdr: (cdr list) → tail (all but first) — alias for cdr-atom
    table.insert_native("cdr", 1, |args, _| {
        expect_n_args(args, 1, "cdr")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => {
                Ok(NDet::single(Atom::Expr(items[1..].to_vec())))
            }
            Atom::Expr(_) => Err("cdr: empty list".into()),
            other => Err(format!("cdr: expected list, got {}", other.to_sexpr_string())),
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

    // first: (first list) → first element — alias for first-from-pair
    table.insert_native("first", 1, |args, _| {
        expect_n_args(args, 1, "first")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("first: empty list".into()),
            other => Err(format!("first: expected list, got {}", other.to_sexpr_string())),
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

    // second: (second list) → second element — alias for second-from-pair
    table.insert_native("second", 1, |args, _| {
        expect_n_args(args, 1, "second")?;
        match &args[0] {
            Atom::Expr(items) if items.len() >= 2 => Ok(NDet::single(items[1].clone())),
            Atom::Expr(_) => Err("second: list too short".into()),
            other => Err(format!("second: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // last: (last list) → last element
    table.insert_native("last", 1, |args, _| {
        expect_n_args(args, 1, "last")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[items.len() - 1].clone())),
            Atom::Expr(_) => Err("last: empty list".into()),
            other => Err(format!("last: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // decons: (decons list) → (first rest) — destructure list into head and tail
    table.insert_native("decons", 1, |args, _| {
        expect_n_args(args, 1, "decons")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => {
                let head = items[0].clone();
                let rest = Atom::Expr(items[1..].to_vec());
                Ok(NDet::single(Atom::Expr(vec![head, rest])))
            }
            Atom::Expr(_) => Err("decons: empty list".into()),
            other => Err(format!("decons: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // reverse: (reverse list) → reversed list
    table.insert_native("reverse", 1, |args, _| {
        expect_n_args(args, 1, "reverse")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut rev = items.clone();
                rev.reverse();
                Ok(NDet::single(Atom::Expr(rev)))
            }
            other => Err(format!("reverse: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // is-member: (is-member elem list) → True/False
    table.insert_native("is-member", 2, |args, _| {
        expect_n_args(args, 2, "is-member")?;
        let found = match &args[1] {
            Atom::Expr(items) => items.iter().any(|x| *x == args[0]),
            other => *other == args[0],
        };
        Ok(NDet::single(if found { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // exclude-item: (exclude-item elem list) → list without elem
    table.insert_native("exclude-item", 2, |args, _| {
        expect_n_args(args, 2, "exclude-item")?;
        match &args[1] {
            Atom::Expr(items) => {
                let filtered: Vec<Atom> = items.iter().filter(|x| **x != args[0]).cloned().collect();
                Ok(NDet::single(Atom::Expr(filtered)))
            }
            other => {
                if *other == args[0] {
                    Ok(NDet::single(Atom::Expr(vec![])))
                } else {
                    Ok(NDet::single(other.clone()))
                }
            }
        }
    });

    // unique-atom: (unique-atom list) → deduplicated list
    table.insert_native("unique-atom", 1, |args, _| {
        expect_n_args(args, 1, "unique-atom")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut seen = Vec::with_capacity(items.len());
                let mut deduped = Vec::with_capacity(items.len());
                for item in items {
                    if !seen.contains(item) {
                        seen.push(item.clone());
                        deduped.push(item.clone());
                    }
                }
                Ok(NDet::single(Atom::Expr(deduped)))
            }
            other => Ok(NDet::single(other.clone())),
        }
    });

    // union-atom: (union-atom list1 list2) → union of two lists (no duplicates)
    table.insert_native("union-atom", 2, |args, _| {
        expect_n_args(args, 2, "union-atom")?;
        let items1 = match &args[0] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let items2 = match &args[1] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let mut result = items1;
        for item in items2 {
            if !result.contains(&item) {
                result.push(item);
            }
        }
        Ok(NDet::single(Atom::Expr(result)))
    });

    // intersection-atom: (intersection-atom list1 list2) → elements in both lists (no duplicates)
    table.insert_native("intersection-atom", 2, |args, _| {
        expect_n_args(args, 2, "intersection-atom")?;
        let items1 = match &args[0] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let items2 = match &args[1] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let mut result = Vec::new();
        for item in &items1 {
            if items2.contains(item) && !result.contains(item) {
                result.push(item.clone());
            }
        }
        Ok(NDet::single(Atom::Expr(result)))
    });

    // subtraction-atom: (subtraction-atom list1 list2) → elements in list1 not in list2 (set difference)
    table.insert_native("subtraction-atom", 2, |args, _| {
        expect_n_args(args, 2, "subtraction-atom")?;
        let items1 = match &args[0] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let items2 = match &args[1] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let result: Vec<Atom> = items1.into_iter().filter(|x| !items2.contains(x)).collect();
        Ok(NDet::single(Atom::Expr(result)))
    });
}

// ---- Helpers ----

fn alpha_equiv(
    a: &Atom,
    b: &Atom,
    map_ab: &mut std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    map_ba: &mut std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
) -> bool {
    match (a, b) {
        (Atom::Sym(sa), Atom::Sym(sb)) => {
            let a_var = sa.starts_with('$');
            let b_var = sb.starts_with('$');
            match (a_var, b_var) {
                (true, true) => {
                    let fwd = map_ab.entry(sa.clone()).or_insert_with(|| sb.clone());
                    let fwd_ok = fwd == sb;
                    let bwd = map_ba.entry(sb.clone()).or_insert_with(|| sa.clone());
                    fwd_ok && bwd == sa
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

