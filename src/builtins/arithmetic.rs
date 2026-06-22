//! Builtins for numeric operations.

use crate::atom::{Atom, Numeric};
use crate::func::{FnTable, NDet};

/// Convert a Numeric to f64 for operations that need a floating-point value.
fn numeric_as_f64(n: &Numeric) -> f64 {
    match n {
        Numeric::Int(i) => i.to_string().parse::<f64>().unwrap_or(f64::NAN),
        Numeric::Dec(d) => d.to_string().parse::<f64>().unwrap_or(f64::NAN),
    }
}

/// Parse an atom as a floating-point number (used by trig/sqrt/etc.).
pub fn atom_as_f64(atom: &Atom, name: &str) -> Result<f64, String> {
    match atom {
        Atom::Num(n) => Ok(numeric_as_f64(n)),
        Atom::Sym(symbol) => symbol
            .parse::<f64>()
            .map_err(|_| format!("{name}: expected number, got {symbol}")),
        other => Err(format!(
            "{name}: expected number, got {}",
            other.to_sexpr_string()
        )),
    }
}

/// Add two Numeric values, promoting to Dec when either operand is Dec.
fn numeric_add(a: &Numeric, b: &Numeric) -> Numeric {
    match (a, b) {
        (Numeric::Int(x), Numeric::Int(y)) => Numeric::Int(x + y),
        _ => {
            let x: dashu::Decimal = a.to_string().parse().unwrap();
            let y: dashu::Decimal = b.to_string().parse().unwrap();
            Numeric::Dec(x + y)
        }
    }
}

/// Subtract two Numeric values, promoting to Dec when either operand is Dec.
fn numeric_sub(a: &Numeric, b: &Numeric) -> Numeric {
    match (a, b) {
        (Numeric::Int(x), Numeric::Int(y)) => Numeric::Int(x - y),
        _ => {
            let x: dashu::Decimal = a.to_string().parse().unwrap();
            let y: dashu::Decimal = b.to_string().parse().unwrap();
            Numeric::Dec(x - y)
        }
    }
}

/// Multiply two Numeric values, promoting to Dec when either operand is Dec.
fn numeric_mul(a: &Numeric, b: &Numeric) -> Numeric {
    match (a, b) {
        (Numeric::Int(x), Numeric::Int(y)) => Numeric::Int(x * y),
        _ => {
            let x: dashu::Decimal = a.to_string().parse().unwrap();
            let y: dashu::Decimal = b.to_string().parse().unwrap();
            Numeric::Dec(x * y)
        }
    }
}

/// Remainder of two Numeric values (integers only; returns error message on Dec).
fn numeric_rem(a: &Numeric, b: &Numeric) -> Result<Numeric, String> {
    match (a, b) {
        (Numeric::Int(x), Numeric::Int(y)) => {
            if *y == dashu::Integer::from(0i32) {
                Err("% by zero".into())
            } else {
                Ok(Numeric::Int(x % y))
            }
        }
        _ => Err("% requires integers".into()),
    }
}

/// Compare two Numeric values. Promotes to Dec for mixed comparisons.
fn numeric_cmp(a: &Numeric, b: &Numeric) -> std::cmp::Ordering {
    match (a, b) {
        (Numeric::Int(x), Numeric::Int(y)) => x.cmp(y),
        _ => {
            let x: dashu::Decimal = a.to_string().parse().unwrap();
            let y: dashu::Decimal = b.to_string().parse().unwrap();
            x.partial_cmp(&y).unwrap_or(std::cmp::Ordering::Equal)
        }
    }
}

/// Convert a floating-point value into an atom preserving integers.
pub fn f64_to_atom(value: f64) -> Atom {
    if value.fract() == 0.0 && value.is_finite() {
        Atom::num(value as i128)
    } else {
        Atom::decimal(&value.to_string()).unwrap_or_else(|_| Atom::sym(&value.to_string()))
    }
}

/// Convert a floating-point value into an atom with a visible decimal part.
pub fn f64_to_float_atom(value: f64) -> Atom {
    let rendered = if value.fract() == 0.0 && value.is_finite() {
        format!("{value:.1}")
    } else {
        value.to_string()
    };
    Atom::decimal(&rendered).unwrap_or_else(|_| Atom::sym(&rendered))
}

/// Check the expected arity for a builtin call.
pub fn expect_n_args(args: &[Atom], n: usize, name: &str) -> Result<(), String> {
    if args.len() != n {
        return Err(format!("{name}: expected {n} args, got {}", args.len()));
    }
    Ok(())
}

/// Alpha-equivalence check: two atoms are alpha-equivalent if they are
/// structurally identical up to consistent variable renaming.
pub(crate) fn alpha_equiv(
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
                && as_
                    .iter()
                    .zip(bs.iter())
                    .all(|(x, y)| alpha_equiv(x, y, map_ab, map_ba))
        }
        _ => false,
    }
}

/// Register arithmetic builtins.
pub fn register_arithmetic_builtins(funcs: &FnTable) {
    funcs.insert_native("+", 2, |args, _| {
        expect_n_args(args, 2, "+")?;
        Ok(NDet::single(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => Atom::Num(numeric_add(a, b)),
            _ => f64_to_atom(atom_as_f64(&args[0], "+")? + atom_as_f64(&args[1], "+")?),
        }))
    });
    funcs.mark_pure("+", 2);

    funcs.insert_native("-", 2, |args, _| {
        expect_n_args(args, 2, "-")?;
        Ok(NDet::single(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => Atom::Num(numeric_sub(a, b)),
            _ => f64_to_atom(atom_as_f64(&args[0], "-")? - atom_as_f64(&args[1], "-")?),
        }))
    });
    funcs.mark_pure("-", 2);

    funcs.insert_native("*", 2, |args, _| {
        expect_n_args(args, 2, "*")?;
        Ok(NDet::single(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => Atom::Num(numeric_mul(a, b)),
            _ => f64_to_atom(atom_as_f64(&args[0], "*")? * atom_as_f64(&args[1], "*")?),
        }))
    });
    funcs.mark_pure("*", 2);

    funcs.insert_native("/", 2, |args, _| {
        expect_n_args(args, 2, "/")?;
        let lhs = atom_as_f64(&args[0], "/")?;
        let rhs = atom_as_f64(&args[1], "/")?;
        Ok(NDet::single(f64_to_float_atom(lhs / rhs)))
    });
    funcs.mark_pure("/", 2);

    funcs.insert_native("%", 2, |args, _| {
        expect_n_args(args, 2, "%")?;
        Ok(NDet::single(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => numeric_rem(a, b)
                    .map(Atom::Num)
                    .unwrap_or_else(|e| Atom::sym(&e)),
            _ => f64_to_atom(atom_as_f64(&args[0], "%")? % atom_as_f64(&args[1], "%")?),
        }))
    });
    funcs.mark_pure("%", 2);

    funcs.insert_native("<", 2, |args, _| {
        expect_n_args(args, 2, "<")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => numeric_cmp(a, b) == std::cmp::Ordering::Less,
            _ => atom_as_f64(&args[0], "<")? < atom_as_f64(&args[1], "<")?,
        })))
    });
    funcs.mark_pure("<", 2);

    funcs.insert_native(">", 2, |args, _| {
        expect_n_args(args, 2, ">")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => numeric_cmp(a, b) == std::cmp::Ordering::Greater,
            _ => atom_as_f64(&args[0], ">")? > atom_as_f64(&args[1], ">")?,
        })))
    });
    funcs.mark_pure(">", 2);

    funcs.insert_native("<=", 2, |args, _| {
        expect_n_args(args, 2, "<=")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => numeric_cmp(a, b) != std::cmp::Ordering::Greater,
            _ => atom_as_f64(&args[0], "<=")? <= atom_as_f64(&args[1], "<=")?,
        })))
    });
    funcs.mark_pure("<=", 2);

    funcs.insert_native(">=", 2, |args, _| {
        expect_n_args(args, 2, ">=")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(match (&args[0], &args[1]) {
            (Atom::Num(a), Atom::Num(b)) => numeric_cmp(a, b) != std::cmp::Ordering::Less,
            _ => atom_as_f64(&args[0], ">=")? >= atom_as_f64(&args[1], ">=")?,
        })))
    });
    funcs.mark_pure(">=", 2);

    // Float math unaries
    funcs.insert_native("sqrt-math", 1, |args, _| {
        let x = atom_as_f64(&args[0], "sqrt-math")?;
        Ok(NDet::single(f64_to_float_atom(x.sqrt())))
    });
    funcs.mark_pure("sqrt-math", 1);
    funcs.insert_native("abs-math", 1, |args, _| {
        Ok(NDet::single(f64_to_atom(atom_as_f64(&args[0], "abs-math")?.abs())))
    });
    funcs.mark_pure("abs-math", 1);
    funcs.insert_native("trunc-math", 1, |args, _| {
        Ok(NDet::single(f64_to_atom(atom_as_f64(&args[0], "trunc-math")?.trunc())))
    });
    funcs.mark_pure("trunc-math", 1);
    funcs.insert_native("ceil-math", 1, |args, _| {
        Ok(NDet::single(f64_to_atom(atom_as_f64(&args[0], "ceil-math")?.ceil())))
    });
    funcs.mark_pure("ceil-math", 1);
    funcs.insert_native("floor-math", 1, |args, _| {
        Ok(NDet::single(f64_to_atom(atom_as_f64(&args[0], "floor-math")?.floor())))
    });
    funcs.mark_pure("floor-math", 1);
    funcs.insert_native("round-math", 1, |args, _| {
        Ok(NDet::single(f64_to_atom(atom_as_f64(&args[0], "round-math")?.round())))
    });
    funcs.mark_pure("round-math", 1);
    funcs.insert_native("sin-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "sin-math")?.sin())))
    });
    funcs.mark_pure("sin-math", 1);
    funcs.insert_native("asin-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "asin-math")?.asin())))
    });
    funcs.mark_pure("asin-math", 1);
    funcs.insert_native("cos-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "cos-math")?.cos())))
    });
    funcs.mark_pure("cos-math", 1);
    funcs.insert_native("acos-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "acos-math")?.acos())))
    });
    funcs.mark_pure("acos-math", 1);
    funcs.insert_native("tan-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "tan-math")?.tan())))
    });
    funcs.mark_pure("tan-math", 1);
    funcs.insert_native("atan-math", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "atan-math")?.atan())))
    });
    funcs.mark_pure("atan-math", 1);
    funcs.insert_native("exp", 1, |args, _| {
        Ok(NDet::single(f64_to_float_atom(atom_as_f64(&args[0], "exp")?.exp())))
    });
    funcs.mark_pure("exp", 1);

    // Float math binaries
    funcs.insert_native("pow-math", 2, |args, _| {
        let a = atom_as_f64(&args[0], "pow-math")?;
        let b = atom_as_f64(&args[1], "pow-math")?;
        Ok(NDet::single(f64_to_atom(a.powf(b))))
    });
    funcs.mark_pure("pow-math", 2);
    funcs.insert_native("log-math", 2, |args, _| {
        let a = atom_as_f64(&args[0], "log-math")?;
        let b = atom_as_f64(&args[1], "log-math")?;
        Ok(NDet::single(f64_to_float_atom(b.log(a))))
    });
    funcs.mark_pure("log-math", 2);
    funcs.insert_native("min", 2, |args, _| {
        let a = atom_as_f64(&args[0], "min")?;
        let b = atom_as_f64(&args[1], "min")?;
        Ok(NDet::single(f64_to_atom(a.min(b))))
    });
    funcs.mark_pure("min", 2);
    funcs.insert_native("max", 2, |args, _| {
        let a = atom_as_f64(&args[0], "max")?;
        let b = atom_as_f64(&args[1], "max")?;
        Ok(NDet::single(f64_to_atom(a.max(b))))
    });
    funcs.mark_pure("max", 2);

    funcs.insert_native("isnan-math", 1, |args, _| {
        let x = atom_as_f64(&args[0], "isnan-math")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(x.is_nan())))
    });
    funcs.mark_pure("isnan-math", 1);

    funcs.insert_native("isinf-math", 1, |args, _| {
        let x = atom_as_f64(&args[0], "isinf-math")?;
        Ok(NDet::single(crate::builtins::boolean::bool_atom(x.is_infinite())))
    });
    funcs.mark_pure("isinf-math", 1);

    funcs.insert_native("min-atom", 1, |args, _| {
        let items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        let mut best = f64::INFINITY;
        for item in &items {
            best = best.min(atom_as_f64(item, "min-atom")?);
        }
        Ok(NDet::single(f64_to_atom(best)))
    });
    funcs.mark_pure("min-atom", 1);

    funcs.insert_native("max-atom", 1, |args, _| {
        let items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        let mut best = f64::NEG_INFINITY;
        for item in &items {
            best = best.max(atom_as_f64(item, "max-atom")?);
        }
        Ok(NDet::single(f64_to_atom(best)))
    });
    funcs.mark_pure("max-atom", 1);

    funcs.insert_native("sort-math", 1, |args, _| {
        expect_n_args(args, 1, "sort-math")?;
        let items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        let mut pairs: Vec<(f64, Atom)> = Vec::with_capacity(items.len());
        for item in &items {
            pairs.push((atom_as_f64(item, "sort-math")?, item.clone()));
        }
        pairs.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        Ok(NDet::single(Atom::Expr(pairs.into_iter().map(|(_, a)| a).collect())))
    });
    funcs.mark_pure("sort-math", 1);

    // random-int Min Max → integer in [Min, Max] inclusive
    // random-int &rng Min Max → same (rng arg ignored, stateless thread_rng)
    funcs.insert_native("random-int", 2, |args, _| {
        let (min, max) = (atom_as_f64(&args[0], "random-int")? as i64,
                         atom_as_f64(&args[1], "random-int")? as i64);
        if min > max { return Err(format!("random-int: min {min} > max {max}")); }
        use rand::Rng;
        let n = rand::thread_rng().gen_range(min..=max);
        Ok(NDet::single(Atom::Num(Numeric::Int(dashu::Integer::from(n)))))
    });

    funcs.insert_native("random-int", 3, |args, _| {
        // args[0] may be &rng symbol — skip it, use args[1]/args[2]
        let (min, max) = (atom_as_f64(&args[1], "random-int")? as i64,
                         atom_as_f64(&args[2], "random-int")? as i64);
        if min > max { return Err(format!("random-int: min {min} > max {max}")); }
        use rand::Rng;
        let n = rand::thread_rng().gen_range(min..=max);
        Ok(NDet::single(Atom::Num(Numeric::Int(dashu::Integer::from(n)))))
    });

    // random-float Min Max → float in [Min, Max)
    // random-float &rng Min Max → same
    funcs.insert_native("random-float", 2, |args, _| {
        let (min, max) = (atom_as_f64(&args[0], "random-float")?,
                         atom_as_f64(&args[1], "random-float")?);
        let r: f64 = rand::random();
        Ok(NDet::single(f64_to_atom(min + r * (max - min))))
    });

    funcs.insert_native("random-float", 3, |args, _| {
        let (min, max) = (atom_as_f64(&args[1], "random-float")?,
                         atom_as_f64(&args[2], "random-float")?);
        let r: f64 = rand::random();
        Ok(NDet::single(f64_to_atom(min + r * (max - min))))
    });
}
