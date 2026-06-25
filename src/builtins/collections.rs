//! Builtins for list-like atom operations.

use crate::atom::Atom;
use crate::func::{FnTable, FunctionKind, NDet};
use std::collections::HashMap;
use std::sync::Arc;

fn expect(args: &[Atom], n: usize, name: &str) -> Result<(), String> {
    crate::builtins::arithmetic::expect_n_args(args, n, name)
}

fn decons_impl(args: &[Atom], _: &FnTable) -> Result<NDet, String> {
    expect(args, 1, "decons")?;
    match &args[0] {
        Atom::Expr(items) if !items.is_empty() => {
            let head = items[0].clone();
            let rest = Atom::Expr(crate::atom::expr_data(&items[1..]));
            Ok(NDet::single(Atom::Expr(crate::atom::expr_data([head, rest]))))
        }
        Atom::Expr(_) => Err("decons: empty list".into()),
        other => Err(format!("decons: expected list, got {}", other.to_sexpr_string())),
    }
}

/// Register collection builtins.
pub fn register_collection_builtins(funcs: &FnTable) {
    funcs.insert_native("size-atom", 1, |args, _| {
        expect(args, 1, "size-atom")?;
        let len = match &args[0] {
            Atom::Expr(items) => items.len(),
            _ => 1,
        };
        Ok(NDet::single(Atom::num(len as i128)))
    });
    funcs.mark_pure("size-atom", 1);

    funcs.insert_native("length", 1, |args, _| {
        expect(args, 1, "length")?;
        let len = match &args[0] {
            Atom::Expr(items) => items.len(),
            _ => 1,
        };
        Ok(NDet::single(Atom::num(len as i128)))
    });
    funcs.mark_pure("length", 1);

    funcs.insert_native("car-atom", 1, |args, _| {
        expect(args, 1, "car-atom")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
        Atom::Expr(_) => {
            crate::eval::shared::debug::logical_failure(|| {
                "warn: car-atom on empty list".to_string()
            });
            Ok(NDet::stream(std::iter::empty()))
        }
        other => {
            crate::eval::shared::debug::logical_failure(|| {
                format!("warn: car-atom: expected list, got {}", other.to_sexpr_string())
            });
            Ok(NDet::stream(std::iter::empty()))
        }
        }
    });
    funcs.mark_pure("car-atom", 1);

    funcs.insert_native("car", 1, |args, _| {
        expect(args, 1, "car")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("car: empty list".into()),
            other => Err(format!("car: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("car", 1);

    funcs.insert_native("cdr-atom", 1, |args, _| {
        expect(args, 1, "cdr-atom")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(Atom::Expr(crate::atom::expr_data(&items[1..])))),
        Atom::Expr(_) => {
            crate::eval::shared::debug::logical_failure(|| {
                "warn: cdr-atom on empty list".to_string()
            });
            Ok(NDet::stream(std::iter::empty()))
        }
        other => {
            crate::eval::shared::debug::logical_failure(|| {
                format!("warn: cdr-atom: expected list, got {}", other.to_sexpr_string())
            });
            Ok(NDet::stream(std::iter::empty()))
        }
        }
    });
    funcs.mark_pure("cdr-atom", 1);

    funcs.insert_native("cdr", 1, |args, _| {
        expect(args, 1, "cdr")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(Atom::Expr(crate::atom::expr_data(&items[1..])))),
            Atom::Expr(_) => Err("cdr: empty list".into()),
            other => Err(format!("cdr: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("cdr", 1);

    funcs.insert_native("cons-atom", 2, |args, _| {
        expect(args, 2, "cons-atom")?;
        let mut out = vec![args[0].clone()];
        match &args[1] {
            Atom::Expr(items) => out.extend(items.iter().cloned()),
            other => out.push(other.clone()),
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(out))))
    });
    funcs.mark_pure("cons-atom", 2);

    funcs.insert_native("cons", 2, |args, _| {
        expect(args, 2, "cons")?;
        let mut out = vec![args[0].clone()];
        match &args[1] {
            Atom::Expr(items) => out.extend(items.iter().cloned()),
            other => out.push(other.clone()),
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(out))))
    });
    funcs.mark_pure("cons", 2);

    funcs.insert_native("decons-atom", 1, decons_impl);
    funcs.mark_pure("decons-atom", 1);

    funcs.insert_native("decons", 1, decons_impl);
    funcs.mark_pure("decons", 1);

    funcs.insert_native("append", 2, |args, _| {
        expect(args, 2, "append")?;
        let mut out = match &args[0] {
            Atom::Expr(items) => items.to_vec(),
            other => vec![other.clone()],
        };
        match &args[1] {
            Atom::Expr(items) => out.extend(items.iter().cloned()),
            other => out.push(other.clone()),
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(out))))
    });
    funcs.mark_pure("append", 2);

    funcs.insert_native("reverse", 1, |args, _| {
        expect(args, 1, "reverse")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut rev = items.to_vec();
                rev.reverse();
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(rev))))
            }
            other => Err(format!("reverse: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("reverse", 1);

    funcs.insert_native("index-atom", 2, |args, _| {
        expect(args, 2, "index-atom")?;
        let idx = match &args[1] {
            Atom::Num(n) => args[1].as_num()
                .and_then(|i| usize::try_from(i).map_err(|_| format!("index-atom: negative index {}", i)))
                .map_err(|_| format!("index-atom: index must be non-negative, got {}", n))?,
            other => return Err(format!("index-atom: index must be a number, got {}", other.to_sexpr_string())),
        };
        match &args[0] {
            Atom::Expr(items) => items.get(idx).cloned().map(NDet::single)
                .ok_or_else(|| format!("index-atom: index {} out of bounds (len {})", idx, items.len())),
            other => Err(format!("index-atom: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("index-atom", 2);

    funcs.insert_native("id", 1, |args, _| {
        expect(args, 1, "id")?;
        Ok(NDet::single(args[0].clone()))
    });
    funcs.mark_pure("id", 1);

    funcs.insert_native("first-from-pair", 1, |args, _| {
        expect(args, 1, "first-from-pair")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("first-from-pair: empty list".into()),
            other => Err(format!("first-from-pair: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("first-from-pair", 1);

    funcs.insert_native("first", 1, |args, _| {
        expect(args, 1, "first")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[0].clone())),
            Atom::Expr(_) => Err("first: empty list".into()),
            other => Err(format!("first: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("first", 1);

    funcs.insert_native("second-from-pair", 1, |args, _| {
        expect(args, 1, "second-from-pair")?;
        match &args[0] {
            Atom::Expr(items) if items.len() >= 2 => Ok(NDet::single(items[1].clone())),
            Atom::Expr(_) => Err("second-from-pair: list too short".into()),
            other => Err(format!("second-from-pair: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("second-from-pair", 1);

    funcs.insert_native("second", 1, |args, _| {
        expect(args, 1, "second")?;
        match &args[0] {
            Atom::Expr(items) if items.len() >= 2 => Ok(NDet::single(items[1].clone())),
            Atom::Expr(_) => Err("second: list too short".into()),
            other => Err(format!("second: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("second", 1);

    funcs.insert_native("last", 1, |args, _| {
        expect(args, 1, "last")?;
        match &args[0] {
            Atom::Expr(items) if !items.is_empty() => Ok(NDet::single(items[items.len() - 1].clone())),
            Atom::Expr(_) => Err("last: empty list".into()),
            other => Err(format!("last: expected list, got {}", other.to_sexpr_string())),
        }
    });
    funcs.mark_pure("last", 1);

    funcs.insert_native("msort", 1, |args, _| {
        expect(args, 1, "msort")?;
        let mut items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        items.sort_by(|a, b| a.to_sexpr_string().cmp(&b.to_sexpr_string()));
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(items))))
    });
    funcs.mark_pure("msort", 1);

    funcs.insert_native("sort", 1, |args, _| {
        expect(args, 1, "sort")?;
        let mut items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        items.sort_by(|a, b| a.to_sexpr_string().cmp(&b.to_sexpr_string()));
        items.dedup();
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(items))))
    });
    funcs.mark_pure("sort", 1);

    funcs.insert_native("sort-atom", 1, |args, _| {
        expect(args, 1, "sort-atom")?;
        let mut items = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            a => vec![a.clone()],
        };
        items.sort_by(|a, b| a.to_sexpr_string().cmp(&b.to_sexpr_string()));
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(items))))
    });
    funcs.mark_pure("sort-atom", 1);

    funcs.insert_native("is-member", 2, |args, _| {
        expect(args, 2, "is-member")?;
        let found = match &args[1] {
            Atom::Expr(items) => items.iter().any(|x| *x == args[0]),
            other => *other == args[0],
        };
        Ok(NDet::single(crate::builtins::boolean::bool_atom(found)))
    });
    funcs.mark_pure("is-member", 2);

    funcs.insert_native("exclude-item", 2, |args, _| {
        expect(args, 2, "exclude-item")?;
        match &args[1] {
            Atom::Expr(items) => {
                let filtered: Vec<Atom> = items.iter().filter(|x| **x != args[0]).cloned().collect();
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(filtered))))
            }
            other => {
                if *other == args[0] {
                    Ok(NDet::single(Atom::Expr(crate::atom::expr_data([]))))
                } else {
                    Ok(NDet::single(other.clone()))
                }
            }
        }
    });
    funcs.mark_pure("exclude-item", 2);

    funcs.insert_native("unique-atom", 1, |args, _| {
        expect(args, 1, "unique-atom")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut seen = Vec::with_capacity(items.len());
                let mut deduped = Vec::with_capacity(items.len());
                for item in items.iter() {
                    if !seen.contains(item) {
                        seen.push(item.clone());
                        deduped.push(item.clone());
                    }
                }
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(deduped))))
            }
            other => Ok(NDet::single(other.clone())),
        }
    });
    funcs.mark_pure("unique-atom", 1);

    funcs.insert_native("alpha-unique-atom", 1, |args, _| {
        expect(args, 1, "alpha-unique-atom")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut deduped: Vec<Atom> = Vec::with_capacity(items.len());
                'outer: for item in items.iter() {
                    for existing in &deduped {
                        let mut map_ab = std::collections::HashMap::new();
                        let mut map_ba = std::collections::HashMap::new();
                        if crate::builtins::arithmetic::alpha_equiv(item, existing, &mut map_ab, &mut map_ba) {
                            continue 'outer;
                        }
                    }
                    deduped.push(item.clone());
                }
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(deduped))))
            }
            other => Ok(NDet::single(other.clone())),
        }
    });
    funcs.mark_pure("alpha-unique-atom", 1);

    funcs.insert_native("union-atom", 2, |args, _| {
        expect(args, 2, "union-atom")?;
        let mut items1 = match &args[0] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let items2: Vec<Atom> = match &args[1] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        items1.extend(items2);
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(items1))))
    });
    funcs.mark_pure("union-atom", 2);

    funcs.insert_native("intersection-atom", 2, |args, _| {
        expect(args, 2, "intersection-atom")?;
        let items1: Vec<Atom> = match &args[0] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let items2: Vec<Atom> = match &args[1] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let mut count2 = HashMap::new();
        for item in &items2 {
            *count2.entry(item.clone()).or_insert(0usize) += 1;
        }
        let mut result = Vec::new();
        for item in &items1 {
            if let Some(c) = count2.get_mut(item) {
                if *c > 0 {
                    result.push(item.clone());
                    *c -= 1;
                }
            }
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(result))))
    });
    funcs.mark_pure("intersection-atom", 2);

    funcs.insert_native("subtraction-atom", 2, |args, _| {
        expect(args, 2, "subtraction-atom")?;
        let items1: Vec<Atom> = match &args[0] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let items2: Vec<Atom> = match &args[1] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let mut count2 = HashMap::new();
        for item in &items2 {
            *count2.entry(item.clone()).or_insert(0usize) += 1;
        }
        let mut result = Vec::new();
        for item in items1 {
            if let Some(c) = count2.get_mut(&item) {
                if *c > 0 {
                    *c -= 1;
                    // skip — this occurrence consumed by subtraction
                } else {
                    result.push(item);
                }
            } else {
                result.push(item);
            }
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(result))))
    });
    funcs.mark_pure("subtraction-atom", 2);

    funcs.insert_native("list_to_set", 1, |args, _| {
        expect(args, 1, "list_to_set")?;
        match &args[0] {
            Atom::Expr(items) => {
                let mut seen = Vec::with_capacity(items.len());
                let mut deduped = Vec::with_capacity(items.len());
                for item in items.iter() {
                    if !seen.contains(item) {
                        seen.push(item.clone());
                        deduped.push(item.clone());
                    }
                }
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(deduped))))
            }
            other => Ok(NDet::single(other.clone())),
        }
    });
    funcs.mark_pure("list_to_set", 1);

    funcs.insert_native("foldl", 3, |args, table| {
        expect(args, 3, "foldl")?;
        let items: Vec<Atom> = match &args[2] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let mut acc = args[1].clone();
        for item in &items {
            let fname = match &args[0] {
                Atom::Sym(s) => s.clone(),
                _ => return Err("foldl: first arg must be a symbol (function name)".into()),
            };
            let func_ref = table.get(&fname, 2)
                .ok_or_else(|| format!("foldl: function {} with arity 2 not found", fname))?;
            let func_ptr = match &func_ref.kind { FunctionKind::Native { func } => func.clone() };
            drop(func_ref);
            let mut result = func_ptr(&[acc, item.clone()], table)?;
            acc = result.next().ok_or_else(|| "foldl: function produced no results".to_string())?;
        }
        Ok(NDet::single(acc))
    });

    // foldl-atom is handled as a special form in dispatch.rs via Frame::FoldlInit/FoldlAtom

    funcs.insert_native("map-atom", 2, |args, table| {
        expect(args, 2, "map-atom")?;
        // map-atom takes (list func) order
        let items: Vec<Atom> = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            other => vec![other.clone()],
        };
        let func_atom = &args[1];
        let mut results = Vec::with_capacity(items.len());
        match func_atom {
            Atom::Sym(fname) => {
                if let Some(function) = table.get(fname, 1) {
                    if let crate::func::FunctionKind::Native { func } = &function.kind {
                        for item in &items {
                            let mut result = func(&[item.clone()], table)?;
                            let val = result.next().ok_or_else(|| {
                                format!("map-atom: function {} produced no result for item {}", fname, item.to_sexpr_string())
                            })?;
                            results.push(val);
                        }
                        return Ok(NDet::single(Atom::Expr(crate::atom::expr_data(results))));
                    }
                }
                // Fallback for user-defined functions
                let fn_expr = crate::parser::atom_to_expr(&Atom::Sym(fname.clone()))
                    .unwrap_or(crate::parser::Expr::Symbol(fname.to_string()));
                for item in &items {
                    let item_expr = crate::parser::atom_to_expr(item)
                        .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                    let call = crate::parser::Expr::List(std::sync::Arc::from([fn_expr.clone(), item_expr]));
                    let body_rs = crate::eval::machine::step::run_rs(
                        std::sync::Arc::new(call),
                        crate::env::Env::new(),
                        table,
                        &mut None,
                    )?;
                    let val = body_rs.into_iter().next().map(|(a, _)| a).ok_or_else(|| {
                        format!("map-atom: function {} produced no result for item {}", fname, item.to_sexpr_string())
                    })?;
                    results.push(val);
                }
            }
            Atom::Expr(parts) if parts.len() == 3 && parts[0] == Atom::sym("partial") => {
                if let Atom::Sym(fn_name) = &parts[1] {
                    let old_args: Vec<Atom> = match &parts[2] {
                        Atom::Expr(v) => v.to_vec(),
                        other => vec![other.clone()],
                    };
                    let fn_expr = crate::parser::atom_to_expr(&Atom::Sym(fn_name.clone()))
                        .unwrap_or(crate::parser::Expr::Symbol(fn_name.to_string()));
                    let mut old_arg_exprs: Vec<crate::parser::Expr> = old_args.iter()
                        .map(|a| crate::parser::atom_to_expr(a)
                            .unwrap_or(crate::parser::Expr::Symbol(a.to_sexpr_string())))
                        .collect();
                    for item in &items {
                        let item_expr = crate::parser::atom_to_expr(item)
                            .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                        let mut call_items = vec![fn_expr.clone()];
                        call_items.extend(old_arg_exprs.clone());
                        call_items.push(item_expr);
                        let call = crate::parser::Expr::List(call_items.into());
                        let body_rs = crate::eval::machine::step::run_rs(
                            std::sync::Arc::new(call),
                            crate::env::Env::new(),
                            table,
                            &mut None,
                        )?;
                        let val = body_rs.into_iter().next().map(|(a, _)| a).ok_or_else(|| {
                            format!("map-atom: partial function produced no result for item {}", item.to_sexpr_string())
                        })?;
                        results.push(val);
                    }
                } else {
                    return Err("map-atom: partial function name must be a symbol".into());
                }
            }
            _ => {
                let func_expr = crate::parser::atom_to_expr(func_atom)
                    .unwrap_or(crate::parser::Expr::Symbol(func_atom.to_sexpr_string()));
                for item in &items {
                    let item_expr = crate::parser::atom_to_expr(item)
                        .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                    let call = crate::parser::Expr::List(std::sync::Arc::from([func_expr.clone(), item_expr]));
                    let body_rs = crate::eval::machine::step::run_rs(
                        std::sync::Arc::new(call),
                        crate::env::Env::new(),
                        table,
                        &mut None,
                    )?;
                    let val = body_rs.into_iter().next().map(|(a, _)| a).ok_or_else(|| {
                        format!("map-atom: function produced no result for item {}", item.to_sexpr_string())
                    })?;
                    results.push(val);
                }
            }
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(results))))
    });

    funcs.insert_native("maplist", 2, |args, table| {
        expect(args, 2, "maplist")?;
        let items: Vec<Atom> = match &args[1] { Atom::Expr(v) => v.to_vec(), other => vec![other.clone()] };
        let fname = match &args[0] {
            Atom::Sym(s) => s.clone(),
            _ => return Err("maplist: first arg must be a symbol (function name)".into()),
        };
        let mut results = Vec::with_capacity(items.len());
        for item in &items {
            let func_ref = table.get(&fname, 1)
                .ok_or_else(|| format!("maplist: function {} with arity 1 not found", fname))?;
            let func_ptr = match &func_ref.kind { FunctionKind::Native { func } => func.clone() };
            drop(func_ref);
            let mut result = func_ptr(&[item.clone()], table)?;
            let val = result.next().ok_or_else(|| format!("maplist: function produced no results for item {}", item.to_sexpr_string()))?;
            results.push(val);
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(results))))
    });

    funcs.insert_native("filter-atom", 2, |args, table| {
        expect(args, 2, "filter-atom")?;
        // ponytail: filter-atom takes (list func) order, mirroring map-atom
        let items: Vec<Atom> = match &args[0] {
            Atom::Expr(v) => v.to_vec(),
            other => vec![other.clone()],
        };
        let func_atom = &args[1];
        let mut results = Vec::with_capacity(items.len());
        match func_atom {
            Atom::Sym(fname) => {
                if let Some(function) = table.get(fname, 1) {
                    if let crate::func::FunctionKind::Native { func } = &function.kind {
                        for item in &items {
                            let mut result = func(&[item.clone()], table)?;
                            if let Some(val) = result.next() {
                                if val.is_truthy() {
                                    results.push(item.clone());
                                }
                            }
                        }
                        return Ok(NDet::single(Atom::Expr(crate::atom::expr_data(results))));
                    }
                }
                // Fallback for user-defined functions
                let fn_expr = crate::parser::atom_to_expr(&Atom::Sym(fname.clone()))
                    .unwrap_or(crate::parser::Expr::Symbol(fname.to_string()));
                for item in &items {
                    let item_expr = crate::parser::atom_to_expr(item)
                        .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                    let call = crate::parser::Expr::List(std::sync::Arc::from([fn_expr.clone(), item_expr]));
                    let body_rs = crate::eval::machine::step::run_rs(
                        std::sync::Arc::new(call),
                        crate::env::Env::new(),
                        table,
                        &mut None,
                    )?;
                    if let Some((val, _)) = body_rs.into_iter().next() {
                        if val.is_truthy() {
                            results.push(item.clone());
                        }
                    }
                }
            }
            Atom::Expr(parts) if parts.len() == 3 && parts[0] == Atom::sym("partial") => {
                if let Atom::Sym(fn_name) = &parts[1] {
                    let old_args: Vec<Atom> = match &parts[2] {
                        Atom::Expr(v) => v.to_vec(),
                        other => vec![other.clone()],
                    };
                    let fn_expr = crate::parser::atom_to_expr(&Atom::Sym(fn_name.clone()))
                        .unwrap_or(crate::parser::Expr::Symbol(fn_name.to_string()));
                    let mut old_arg_exprs: Vec<crate::parser::Expr> = old_args.iter()
                        .map(|a| crate::parser::atom_to_expr(a)
                            .unwrap_or(crate::parser::Expr::Symbol(a.to_sexpr_string())))
                        .collect();
                    for item in &items {
                        let item_expr = crate::parser::atom_to_expr(item)
                            .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                        let mut call_items = vec![fn_expr.clone()];
                        call_items.extend(old_arg_exprs.clone());
                        call_items.push(item_expr);
                        let call = crate::parser::Expr::List(call_items.into());
                        let body_rs = crate::eval::machine::step::run_rs(
                            std::sync::Arc::new(call),
                            crate::env::Env::new(),
                            table,
                            &mut None,
                        )?;
                        if let Some((val, _)) = body_rs.into_iter().next() {
                            if val.is_truthy() {
                                    results.push(item.clone());
                            }
                        }
                    }
                } else {
                    return Err("filter-atom: partial function name must be a symbol".into());
                }
            }
            _ => {
                let func_expr = crate::parser::atom_to_expr(func_atom)
                    .unwrap_or(crate::parser::Expr::Symbol(func_atom.to_sexpr_string()));
                for item in &items {
                    let item_expr = crate::parser::atom_to_expr(item)
                        .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
                    let call = crate::parser::Expr::List(std::sync::Arc::from([func_expr.clone(), item_expr]));
                    let body_rs = crate::eval::machine::step::run_rs(
                        std::sync::Arc::new(call),
                        crate::env::Env::new(),
                        table,
                        &mut None,
                    )?;
                    if let Some((val, _)) = body_rs.into_iter().next() {
                        if val.is_truthy() {
                            results.push(item.clone());
                        }
                    }
                }
            }
        }
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(results))))
    });

    funcs.insert_native("concat", 2, |args, _| {
        expect(args, 2, "concat")?;
        match (&args[0], &args[1]) {
            (Atom::Expr(a), Atom::Expr(b)) => {
                let mut out = a.to_vec();
                out.extend(b.iter().cloned());
                Ok(NDet::single(Atom::Expr(crate::atom::expr_data(out))))
            }
            (Atom::Sym(a), Atom::Sym(b)) => Ok(NDet::single(Atom::sym(&format!("{a}{b}")))),
            _ => Ok(NDet::single(Atom::sym(&format!("{}{}", args[0].to_sexpr_string(), args[1].to_sexpr_string())))),
        }
    });
    funcs.mark_pure("concat", 2);

    funcs.insert_native("atom_concat", 2, |args, _| {
        expect(args, 2, "atom_concat")?;
        Ok(NDet::single(Atom::sym(&format!("{}{}", args[0].to_sexpr_string(), args[1].to_sexpr_string()))))
    });
    funcs.mark_pure("atom_concat", 2);

    funcs.insert_native("atom_chars", 1, |args, _| {
        expect(args, 1, "atom_chars")?;
        let chars: Vec<Atom> = args[0].to_sexpr_string().chars().map(|c| Atom::sym(&c.to_string())).collect();
        Ok(NDet::single(Atom::Expr(crate::atom::expr_data(chars))))
    });
    funcs.mark_pure("atom_chars", 1);

    funcs.insert_native("term_hash", 1, |args, _| {
        expect(args, 1, "term_hash")?;
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        args[0].hash(&mut hasher);
        Ok(NDet::single(Atom::num(hasher.finish() as i128)))
    });
    funcs.mark_pure("term_hash", 1);
}
