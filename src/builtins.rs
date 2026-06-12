/// Built-in (grounded) functions: arithmetic, comparison, test, space ops.
///
/// Following maintainability rules: builtins are a single table,
/// macro-registered — one line per function.

use crate::atom::Atom;
use crate::func::{FnTable, FunctionKind, NDet};
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
            Ok(NDet::single(match (&args[0], &args[1]) {
                (Atom::Num(a), Atom::Num(b)) => Atom::Num($int_op(*a, *b)),
                _ => {
                    let a = atom_as_f64(&args[0], $name)?;
                    let b = atom_as_f64(&args[1], $name)?;
                    f64_to_atom($float_op(a, b))
                }
            }))
        });
        $table.mark_pure($name, 2);
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
        $table.mark_pure($name, 2);
    };
}

macro_rules! math_unary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 1, |args, _| {
            let x = atom_as_f64(&args[0], $name)?;
            Ok(NDet::single(f64_to_atom($op(x))))
        });
        $table.mark_pure($name, 1);
    };
}

macro_rules! math_binary {
    ($table:ident, $name:expr, $op:expr) => {
        $table.insert_native($name, 2, |args, _| {
            let a = atom_as_f64(&args[0], $name)?;
            let b = atom_as_f64(&args[1], $name)?;
            Ok(NDet::single(f64_to_atom($op(a, b))))
        });
        $table.mark_pure($name, 2);
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

    // implies truth table (boolean implication)
    bool_clause!(table, "implies", ["True",  "True"],  "True");
    bool_clause!(table, "implies", ["True",  "False"], "False");
    bool_clause!(table, "implies", ["False", "True"],  "True");
    bool_clause!(table, "implies", ["False", "False"], "True");

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
    // get-atoms: (get-atoms space) → stream of all atoms in the space
    // Returns each atom as a separate result so that (collapse (get-atoms &self))
    // collects them into a flat list, matching the match+collapse pattern.
    table.insert_native("get-atoms", 1, |args, table| {
        expect_n_args(args, 1, "get-atoms")?;
        let atoms = table.space.lock().unwrap().get_atoms();
        Ok(NDet::stream(atoms.into_iter()))
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

    // =: (= a b) → True/False — unification-as-boolean (same as == for ground atoms)
    table.insert_native("=", 2, |args, _| {
        expect_n_args(args, 2, "=")?;
        Ok(NDet::single(if args[0] == args[1] {
            Atom::sym("True")
        } else {
            Atom::sym("False")
        }))
    });

    // =?: (=? a b) → True/False — double-negation unification check (same as == for ground atoms)
    table.insert_native("=?", 2, |args, _| {
        expect_n_args(args, 2, "=?")?;
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
        let state = table.state.lock().unwrap();
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
                table.state.lock().unwrap().insert(key, args[1].clone());
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
                table.state.lock().unwrap().insert(key, value);
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

    // sort-atom: (sort-atom list) → lexicographically sorted list (keeps duplicates) — alias for msort
    table.insert_native("sort-atom", 1, |args, _| {
        expect_n_args(args, 1, "sort-atom")?;
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut sorted = items;
        sorted.sort_by(|a, b| a.to_sexpr_string().cmp(&b.to_sexpr_string()));
        Ok(NDet::single(Atom::Expr(sorted)))
    });

    // sort-math: (sort-math list) → numerically sorted list
    table.insert_native("sort-math", 1, |args, _| {
        expect_n_args(args, 1, "sort-math")?;
        let items = match &args[0] {
            Atom::Expr(v) => v.clone(),
            a => vec![a.clone()],
        };
        let mut pairs: Vec<(f64, Atom)> = Vec::with_capacity(items.len());
        for item in &items {
            let num = atom_as_f64(item, "sort-math")?;
            pairs.push((num, item.clone()));
        }
        pairs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        let sorted: Vec<Atom> = pairs.into_iter().map(|(_, a)| a).collect();
        Ok(NDet::single(Atom::Expr(sorted)))
    });

    // same: (same a b) → True/False — structural equality, alias for ==
    table.insert_native("same", 2, |args, _| {
        expect_n_args(args, 2, "same")?;
        Ok(NDet::single(if args[0] == args[1] {
            Atom::sym("True")
        } else {
            Atom::sym("False")
        }))
    });

    // foldl: (foldl func init list) → left fold over a list
    table.insert_native("foldl", 3, |args, table| {
        expect_n_args(args, 3, "foldl")?;
        let items = match &args[2] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let mut acc = args[1].clone();
        for item in &items {
            let fname = match &args[0] {
                Atom::Sym(s) => s.clone(),
                _ => return Err("foldl: first arg must be a symbol (function name)".into()),
            };
            let func_ref = table.get(&fname, 2)
                .ok_or_else(|| format!("foldl: function {} with arity 2 not found", fname))?;
            let func_ptr = match &func_ref.kind {
                FunctionKind::Native { func } => func.clone(),
                FunctionKind::UserDefined { .. } => {
                    return Err("foldl: only native functions supported as first argument".into());
                }
            };
            drop(func_ref);
            let mut result = func_ptr(&[acc, item.clone()], table)?;
            acc = result.next().ok_or_else(|| "foldl: function produced no results".to_string())?;
        }
        Ok(NDet::single(acc))
    });

    // foldl-atom: (foldl-atom func init list) → left fold over a list — alias for foldl
    table.insert_native("foldl-atom", 3, |args, table| {
        expect_n_args(args, 3, "foldl-atom")?;
        let items = match &args[2] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let mut acc = args[1].clone();
        for item in &items {
            let fname = match &args[0] {
                Atom::Sym(s) => s.clone(),
                _ => return Err("foldl-atom: first arg must be a symbol (function name)".into()),
            };
            let func_ref = table.get(&fname, 2)
                .ok_or_else(|| format!("foldl-atom: function {} with arity 2 not found", fname))?;
            let func_ptr = match &func_ref.kind {
                FunctionKind::Native { func } => func.clone(),
                FunctionKind::UserDefined { .. } => {
                    return Err("foldl-atom: only native functions supported as first argument".into());
                }
            };
            drop(func_ref);
            let mut result = func_ptr(&[acc, item.clone()], table)?;
            acc = result.next().ok_or_else(|| "foldl-atom: function produced no results".to_string())?;
        }
        Ok(NDet::single(acc))
    });

    // decons-atom: (decons-atom list) → (first rest) — split list into head and tail, alias for decons
    table.insert_native("decons-atom", 1, |args, _| {
        expect_n_args(args, 1, "decons-atom")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => {
                let head = items[0].clone();
                let rest = Atom::Expr(items[1..].to_vec());
                Ok(NDet::single(Atom::Expr(vec![head, rest])))
            }
            Atom::Expr(_) => Err("decons-atom: empty list".into()),
            other => Err(format!("decons-atom: expected list, got {}", other.to_sexpr_string())),
        }
    });

    // list_to_set: (list_to_set list) → deduplicated list — alias for unique-atom
    table.insert_native("list_to_set", 1, |args, _| {
        expect_n_args(args, 1, "list_to_set")?;
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

    // alpha-unique-atom: (alpha-unique-atom list) → deduplicated list (alpha-equivalence aware)
    table.insert_native("alpha-unique-atom", 1, |args, _| {
        expect_n_args(args, 1, "alpha-unique-atom")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut deduped: Vec<Atom> = Vec::with_capacity(items.len());
                'outer: for item in items {
                    for existing in &deduped {
                        let mut map_ab = std::collections::HashMap::new();
                        let mut map_ba = std::collections::HashMap::new();
                        if alpha_equiv(item, existing, &mut map_ab, &mut map_ba) {
                            continue 'outer;
                        }
                    }
                    deduped.push(item.clone());
                }
                Ok(NDet::single(Atom::Expr(deduped)))
            }
            other => Ok(NDet::single(other.clone())),
        }
    });

    // maplist: (maplist func list) → list of results — apply func (arity 1) to each element
    table.insert_native("maplist", 2, |args, table| {
        expect_n_args(args, 2, "maplist")?;
        let items = match &args[1] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let fname = match &args[0] {
            Atom::Sym(s) => s.clone(),
            _ => return Err("maplist: first arg must be a symbol (function name)".into()),
        };
        let mut results = Vec::with_capacity(items.len());
        for item in &items {
            let func_ref = table.get(&fname, 1)
                .ok_or_else(|| format!("maplist: function {} with arity 1 not found", fname))?;
            let func_ptr = match &func_ref.kind {
                FunctionKind::Native { func } => func.clone(),
                FunctionKind::UserDefined { .. } => {
                    return Err("maplist: only native functions supported as first argument".into());
                }
            };
            drop(func_ref);
            let mut result = func_ptr(&[item.clone()], table)?;
            let val = result.next().ok_or_else(|| format!("maplist: function produced no results for item {}", item.to_sexpr_string()))?;
            results.push(val);
        }
        Ok(NDet::single(Atom::Expr(results)))
    });

    // filter-atom: (filter-atom pred list) → filtered list — keep elements where pred returns True
    table.insert_native("filter-atom", 2, |args, table| {
        expect_n_args(args, 2, "filter-atom")?;
        let items = match &args[1] {
            Atom::Expr(v) => v.clone(),
            other => vec![other.clone()],
        };
        let fname = match &args[0] {
            Atom::Sym(s) => s.clone(),
            _ => return Err("filter-atom: first arg must be a symbol (function name)".into()),
        };
        let mut results = Vec::with_capacity(items.len());
        for item in &items {
            let func_ref = table.get(&fname, 1)
                .ok_or_else(|| format!("filter-atom: function {} with arity 1 not found", fname))?;
            let func_ptr = match &func_ref.kind {
                FunctionKind::Native { func } => func.clone(),
                FunctionKind::UserDefined { .. } => {
                    return Err("filter-atom: only native functions supported as first argument".into());
                }
            };
            drop(func_ref);
            let mut result = func_ptr(&[item.clone()], table)?;
            if let Some(val) = result.next() {
                if val == Atom::sym("True") {
                    results.push(item.clone());
                }
            }
        }
        Ok(NDet::single(Atom::Expr(results)))
    });

    // is-var: (is-var x) → True/False — whether x is a variable (starts with $)
    table.insert_native("is-var", 1, |args, _| {
        expect_n_args(args, 1, "is-var")?;
        let is_var = matches!(&args[0], Atom::Sym(s) if s.starts_with('$'));
        Ok(NDet::single(if is_var { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // is-expr: (is-expr x) → True/False — whether x is a list/expression
    table.insert_native("is-expr", 1, |args, _| {
        expect_n_args(args, 1, "is-expr")?;
        Ok(NDet::single(if matches!(&args[0], Atom::Expr(_)) { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // is-space: (is-space x) → True/False — whether x is a space reference (&...)
    table.insert_native("is-space", 1, |args, _| {
        expect_n_args(args, 1, "is-space")?;
        let is_space = matches!(&args[0], Atom::Sym(s) if s.starts_with('&'));
        Ok(NDet::single(if is_space { Atom::sym("True") } else { Atom::sym("False") }))
    });

    // concat: (concat a b) → concatenation of string syms or lists
    table.insert_native("concat", 2, |args, _| {
        expect_n_args(args, 2, "concat")?;
        match (&args[0], &args[1]) {
            (Atom::Expr(a), Atom::Expr(b)) => {
                let mut out = a.clone();
                out.extend(b.iter().cloned());
                Ok(NDet::single(Atom::Expr(out)))
            }
            (Atom::Sym(a), Atom::Sym(b)) => {
                let s = format!("{}{}", a, b);
                Ok(NDet::single(Atom::sym(&s)))
            }
            _ => {
                // Fallback: concat as strings via sexpr representation
                let s = format!("{}{}", args[0].to_sexpr_string(), args[1].to_sexpr_string());
                Ok(NDet::single(Atom::sym(&s)))
            }
        }
    });

    // atom_concat: (atom_concat a b) → concatenates two atoms into one symbol
    table.insert_native("atom_concat", 2, |args, _| {
        expect_n_args(args, 2, "atom_concat")?;
        let a_str = args[0].to_sexpr_string();
        let b_str = args[1].to_sexpr_string();
        let s = format!("{}{}", a_str, b_str);
        Ok(NDet::single(Atom::sym(&s)))
    });

    // atom_chars: (atom_chars atom) → list of single-char symbols
    table.insert_native("atom_chars", 1, |args, _| {
        expect_n_args(args, 1, "atom_chars")?;
        let s = args[0].to_sexpr_string();
        let chars: Vec<Atom> = s.chars().map(|c| Atom::sym(&c.to_string())).collect();
        Ok(NDet::single(Atom::Expr(chars)))
    });

    // term_hash: (term_hash x) → hash number for the atom
    table.insert_native("term_hash", 1, |args, _| {
        expect_n_args(args, 1, "term_hash")?;
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        args[0].hash(&mut hasher);
        Ok(NDet::single(Atom::Num(hasher.finish() as i128)))
    });

    // sread: (sread str) → parse string into a MeTTa expression atom
    table.insert_native("sread", 1, |args, _| {
        expect_n_args(args, 1, "sread")?;
        let input = match &args[0] {
            Atom::Sym(s) => s.to_string(),
            other => other.to_sexpr_string(),
        };
        // Parse a single atom from string using a simple parser
        Ok(NDet::single(sread_parse(&input)?))
    });

    // Mark pure functions (no side effects on space/state/I/O).
    // Macro-generated builtins (+ - * / < > <= >= sqrt-math etc.) are
    // already marked by their macros. Inline insert_native pure functions
    // are marked here.
    let pure_list: &[(&str, u8)] = &[
        ("!=", 2), ("isnan-math", 1), ("isinf-math", 1),
        ("min-atom", 1), ("max-atom", 1),
        ("size-atom", 1), ("length", 1), ("append", 2),
        ("msort", 1), ("sort", 1),
        ("==", 2), ("=", 2), ("=?", 2),
        ("test", 2), ("repr", 1),
        ("cons-atom", 2), ("cons", 2),
        ("car-atom", 1), ("car", 1),
        ("cdr-atom", 1), ("cdr", 1),
        ("index-atom", 2), ("id", 1), ("=alpha", 2),
        ("first-from-pair", 1), ("first", 1),
        ("second-from-pair", 1), ("second", 1),
        ("last", 1), ("decons", 1),
        ("reverse", 1), ("is-member", 2),
        ("exclude-item", 2), ("unique-atom", 1),
        ("union-atom", 2), ("intersection-atom", 2),
        ("subtraction-atom", 2),
        ("sort-atom", 1), ("sort-math", 1),
        ("same", 2),
        ("decons-atom", 1), ("list_to_set", 1),
        ("alpha-unique-atom", 1),
        ("is-var", 1), ("is-expr", 1), ("is-space", 1),
        ("concat", 2), ("atom_concat", 2), ("atom_chars", 1),
        ("term_hash", 1), ("sread", 1),
        // Boolean functions (user-defined clauses, pure)
        ("or", 2), ("and", 2), ("not", 1), ("xor", 2), ("implies", 2),
    ];
    for &(name, arity) in pure_list {
        table.mark_pure(name, arity);
    }
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


/// Parse a single MeTTa atom from a string.
/// Handles symbols, numbers, and s-expressions.
fn sread_parse(input: &str) -> Result<Atom, String> {
    let input = input.trim();
    if input.is_empty() {
        return Err("sread: empty input".into());
    }
    // Try as sexpr: must start with '(' and end with ')'
    if input.starts_with('(') && input.ends_with(')') {
        let inner = &input[1..input.len() - 1].trim();
        if inner.is_empty() {
            return Ok(Atom::Expr(vec![]));
        }
        // Split on whitespace respecting nested parens
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
                        let token = &inner[start..i];
                        items.push(sread_parse(token)?);
                        start = i + 1;
                    } else if depth == 0 {
                        start = i + 1;
                    }
                }
                _ => {}
            }
        }
        // Last token
        if start < inner.len() {
            let token = inner[start..].trim();
            if !token.is_empty() {
                items.push(sread_parse(token)?);
            }
        }
        return Ok(Atom::Expr(items));
    }
    // Try as number
    if let Ok(n) = input.parse::<i128>() {
        return Ok(Atom::Num(n));
    }
    // Otherwise it's a symbol
    Ok(Atom::sym(input))
}
