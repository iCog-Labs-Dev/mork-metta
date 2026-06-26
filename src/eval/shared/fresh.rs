use crate::atom::Atom;
use crate::parser::Expr;
use rustc_hash::FxHashMap as HashMap;
use rustc_hash::FxHashSet;
use std::sync::atomic::{AtomicU64, Ordering};

const FRESH_PREFIX: &str = "$__fresh";
static FRESH_COUNTER: AtomicU64 = AtomicU64::new(1);

fn next_fresh_name(name_hint: &str) -> String {
    let id = FRESH_COUNTER.fetch_add(1, Ordering::Relaxed);
    let hint = name_hint.strip_prefix('$').unwrap_or(name_hint);
    format!("{FRESH_PREFIX}_{hint}_{id}")
}

fn is_var_symbol(symbol: &str) -> bool {
    symbol.starts_with('$')
}

pub(crate) fn contains_fresh_vars(atom: &Atom) -> bool {
    match atom {
        Atom::Sym(s) => is_generated_var_name(s),
        Atom::Expr(items) => items.iter().any(contains_fresh_vars),
        _ => false,
    }
}

pub(crate) fn is_generated_var_name(name: &str) -> bool {
    name.starts_with(FRESH_PREFIX)
}

fn collect_pattern_vars(expr: &Expr, set: &mut FxHashSet<String>) {
    match expr {
        Expr::Symbol(s) if is_var_symbol(s) => {
            set.insert(s.clone());
        }
        Expr::List(items) => {
            for item in items.iter() {
                collect_pattern_vars(item, set);
            }
        }
        _ => {}
    }
}

fn freshen_symbol(
    symbol: &str,
    bound_vars: &FxHashSet<String>,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> String {
    if let Some(mapped) = locals.get(symbol) {
        return mapped.clone();
    }
    // query the local bound parameters HashSet (very small!)
    if bound_vars.contains(symbol) {
        return symbol.to_string();
    }
    free.entry(symbol.to_string())
        .or_insert_with(|| next_fresh_name(symbol))
        .clone()
}

fn bind_pattern_vars_opt(
    expr: &Expr,
    locals: &mut HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Option<Expr> {
    match expr {
        Expr::Symbol(symbol) if is_var_symbol(symbol) => {
            let fresh = locals
                .entry(symbol.clone())
                .or_insert_with(|| {
                    free.remove(symbol);
                    next_fresh_name(symbol)
                })
                .clone();
            Some(Expr::Symbol(fresh))
        }
        Expr::List(items) => {
            let mut new_items = None;
            for (i, item) in items.iter().enumerate() {
                if let Some(new_item) = bind_pattern_vars_opt(item, locals, free) {
                    if new_items.is_none() {
                        new_items = Some(items[..i].to_vec());
                    }
                    new_items.as_mut().unwrap().push(new_item);
                } else if let Some(ref mut vec) = new_items {
                    vec.push(item.clone());
                }
            }
            new_items.map(|vec| Expr::List(vec.into()))
        }
        _ => None,
    }
}

fn freshen_list(
    items: &[Expr],
    bound_vars: &FxHashSet<String>,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Option<Expr> {
    if items.is_empty() {
        return None;
    }

    if let Expr::Symbol(head) = &items[0] {
        match head.as_str() {
            "quote" => return None,
            "let" if items.len() == 4 => {
                let value_opt = freshen_expr_inner_opt(&items[2], bound_vars, locals, free);
                let mut body_locals = locals.clone();
                let pattern_opt = bind_pattern_vars_opt(&items[1], &mut body_locals, free);
                let body_opt = freshen_expr_inner_opt(&items[3], bound_vars, &body_locals, free);
                if value_opt.is_some() || pattern_opt.is_some() || body_opt.is_some() {
                    let pattern = pattern_opt.unwrap_or_else(|| items[1].clone());
                    let value = value_opt.unwrap_or_else(|| items[2].clone());
                    let body = body_opt.unwrap_or_else(|| items[3].clone());
                    return Some(Expr::List(
                        vec![items[0].clone(), pattern, value, body].into(),
                    ));
                }
                return None;
            }
            "let*" if items.len() == 3 => {
                let Expr::List(bindings) = &items[1] else {
                    return freshen_items_lazy(items, bound_vars, locals, free);
                };
                let mut cur_locals = locals.clone();
                let mut new_bindings = None;
                for (i, binding) in bindings.iter().enumerate() {
                    let Expr::List(pair) = binding else {
                        if let Some(new_b) = freshen_expr_inner_opt(binding, bound_vars, &cur_locals, free) {
                            if new_bindings.is_none() {
                                new_bindings = Some(bindings[..i].to_vec());
                            }
                            new_bindings.as_mut().unwrap().push(new_b);
                        } else if let Some(ref mut vec) = new_bindings {
                            vec.push(binding.clone());
                        }
                        continue;
                    };
                    if pair.len() != 2 {
                        if let Some(new_b) = freshen_expr_inner_opt(binding, bound_vars, &cur_locals, free) {
                            if new_bindings.is_none() {
                                new_bindings = Some(bindings[..i].to_vec());
                            }
                            new_bindings.as_mut().unwrap().push(new_b);
                        } else if let Some(ref mut vec) = new_bindings {
                            vec.push(binding.clone());
                        }
                        continue;
                    }
                    let value_opt = freshen_expr_inner_opt(&pair[1], bound_vars, &cur_locals, free);
                    let pattern_opt = bind_pattern_vars_opt(&pair[0], &mut cur_locals, free);
                    if value_opt.is_some() || pattern_opt.is_some() {
                        if new_bindings.is_none() {
                            new_bindings = Some(bindings[..i].to_vec());
                        }
                        let pattern = pattern_opt.unwrap_or_else(|| pair[0].clone());
                        let value = value_opt.unwrap_or_else(|| pair[1].clone());
                        new_bindings.as_mut().unwrap().push(Expr::List(vec![pattern, value].into()));
                    } else if let Some(ref mut vec) = new_bindings {
                        vec.push(binding.clone());
                    }
                }
                let body_opt = freshen_expr_inner_opt(&items[2], bound_vars, &cur_locals, free);
                if new_bindings.is_some() || body_opt.is_some() {
                    let bindings_expr = match new_bindings {
                        Some(vec) => Expr::List(vec.into()),
                        None => items[1].clone(),
                    };
                    let body = body_opt.unwrap_or_else(|| items[2].clone());
                    return Some(Expr::List(
                        vec![items[0].clone(), bindings_expr, body].into(),
                    ));
                }
                return None;
            }
            "|->" if items.len() == 2 => {
                let mut body_locals = locals.clone();
                let params_opt = bind_pattern_vars_opt(&items[0], &mut body_locals, free);
                let body_opt = freshen_expr_inner_opt(&items[1], bound_vars, &body_locals, free);
                if params_opt.is_some() || body_opt.is_some() {
                    let params = params_opt.unwrap_or_else(|| items[0].clone());
                    let body = body_opt.unwrap_or_else(|| items[1].clone());
                    return Some(Expr::List(vec![params, body].into()));
                }
                return None;
            }
            _ => {}
        }
    }

    freshen_items_lazy(items, bound_vars, locals, free)
}

fn freshen_items_lazy(
    items: &[Expr],
    bound_vars: &FxHashSet<String>,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Option<Expr> {
    let mut new_items = None;
    for (i, item) in items.iter().enumerate() {
        if let Some(new_item) = freshen_expr_inner_opt(item, bound_vars, locals, free) {
            if new_items.is_none() {
                new_items = Some(items[..i].to_vec());
            }
            new_items.as_mut().unwrap().push(new_item);
        } else if let Some(ref mut vec) = new_items {
            vec.push(item.clone());
        }
    }
    new_items.map(|vec| Expr::List(vec.into()))
}

fn has_variables(expr: &Expr) -> bool {
    match expr {
        Expr::Symbol(s) => s.starts_with('$'),
        Expr::List(items) => items.iter().any(has_variables),
        _ => false,
    }
}

fn freshen_expr_inner_opt(
    expr: &Expr,
    bound_vars: &FxHashSet<String>,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Option<Expr> {
    let _profile = crate::profile::ProfileGuard::new_owned("freshen_expr_inner");
    match expr {
        Expr::Symbol(symbol) if is_var_symbol(symbol) => {
            let fresh = freshen_symbol(symbol, bound_vars, locals, free);
            if fresh != *symbol {
                Some(Expr::Symbol(fresh))
            } else {
                None
            }
        }
        Expr::List(items) => freshen_list(items, bound_vars, locals, free),
        _ => None,
    }
}

/// Rename unbound variables in an expression to fresh runtime variables.
///
/// Bound variables are identified from `patterns` (the function parameters).
/// Local binders in a few core forms (`let`, `let*`, `|->`) are handled so
/// shadowing remains correct.
pub(crate) fn rename_apart_unbound_vars(expr: &Expr, patterns: &[Expr]) -> Expr {
    // check has_variables only at the root entry point
    if !has_variables(expr) {
        return expr.clone();
    }
    let mut bound_vars = FxHashSet::default();
    for pat in patterns {
        collect_pattern_vars(pat, &mut bound_vars);
    }
    let mut free = HashMap::default();
    let locals = HashMap::default();
    freshen_expr_inner_opt(expr, &bound_vars, &locals, &mut free).unwrap_or_else(|| expr.clone())
}
