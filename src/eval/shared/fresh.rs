//! Fresh runtime-variable generation and rename-apart helpers.

use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use std::collections::HashMap;
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

fn freshen_symbol(
    symbol: &str,
    env: &Env,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> String {
    if let Some(mapped) = locals.get(symbol) {
        return mapped.clone();
    }
    if crate::eval::shared::env::lookup(env, symbol).is_some() {
        return symbol.to_string();
    }
    free.entry(symbol.to_string())
        .or_insert_with(|| next_fresh_name(symbol))
        .clone()
}

fn bind_pattern_vars(
    expr: &Expr,
    locals: &mut HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Expr {
    match expr {
        Expr::Symbol(symbol) if is_var_symbol(symbol) => {
            let fresh = locals
                .entry(symbol.clone())
                .or_insert_with(|| {
                    free.remove(symbol);
                    next_fresh_name(symbol)
                })
                .clone();
            Expr::Symbol(fresh)
        }
        Expr::List(items) => Expr::List(
            items.iter()
                .map(|item| bind_pattern_vars(item, locals, free))
                .collect::<Vec<_>>()
                .into(),
        ),
        other => other.clone(),
    }
}

fn freshen_list(
    items: &[Expr],
    env: &Env,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Expr {
    if items.is_empty() {
        return Expr::List(Vec::<Expr>::new().into());
    }

    if let Expr::Symbol(head) = &items[0] {
        match head.as_str() {
            "quote" => return Expr::List(items.to_vec().into()),
            "let" if items.len() == 4 => {
                let value = freshen_expr_inner(&items[2], env, locals, free);
                let mut body_locals = locals.clone();
                let pattern = bind_pattern_vars(&items[1], &mut body_locals, free);
                let body = freshen_expr_inner(&items[3], env, &body_locals, free);
                return Expr::List(
                    vec![items[0].clone(), pattern, value, body].into(),
                );
            }
            "let*" if items.len() == 3 => {
                let Expr::List(bindings) = &items[1] else {
                    return Expr::List(
                        items.iter()
                            .map(|item| freshen_expr_inner(item, env, locals, free))
                            .collect::<Vec<_>>()
                            .into(),
                    );
                };
                let mut cur_locals = locals.clone();
                let mut out_bindings = Vec::with_capacity(bindings.len());
                for binding in bindings.iter() {
                    let Expr::List(pair) = binding else {
                        out_bindings.push(freshen_expr_inner(binding, env, &cur_locals, free));
                        continue;
                    };
                    if pair.len() != 2 {
                        out_bindings.push(freshen_expr_inner(binding, env, &cur_locals, free));
                        continue;
                    }
                    let value = freshen_expr_inner(&pair[1], env, &cur_locals, free);
                    let pattern = bind_pattern_vars(&pair[0], &mut cur_locals, free);
                    out_bindings.push(Expr::List(vec![pattern, value].into()));
                }
                let body = freshen_expr_inner(&items[2], env, &cur_locals, free);
                return Expr::List(
                    vec![items[0].clone(), Expr::List(out_bindings.into()), body].into(),
                );
            }
            "|->" if items.len() == 2 => {
                let mut body_locals = locals.clone();
                let params = bind_pattern_vars(&items[0], &mut body_locals, free);
                let body = freshen_expr_inner(&items[1], env, &body_locals, free);
                return Expr::List(vec![items[0].clone(), params, body].into());
            }
            _ => {}
        }
    }

    Expr::List(
        items.iter()
            .map(|item| freshen_expr_inner(item, env, locals, free))
            .collect::<Vec<_>>()
            .into(),
    )
}

fn freshen_expr_inner(
    expr: &Expr,
    env: &Env,
    locals: &HashMap<String, String>,
    free: &mut HashMap<String, String>,
) -> Expr {
    match expr {
        Expr::Symbol(symbol) if is_var_symbol(symbol) => {
            Expr::Symbol(freshen_symbol(symbol, env, locals, free))
        }
        Expr::List(items) => freshen_list(items, env, locals, free),
        other => other.clone(),
    }
}

/// Rename unbound variables in an expression to fresh runtime variables.
///
/// Bound variables already present in `env` are preserved. Local binders in a
/// few core forms (`let`, `let*`, `|->`) are handled so shadowing remains
/// correct within the expression being renamed apart.
pub(crate) fn rename_apart_unbound_vars(expr: &Expr, env: &Env) -> Expr {
    let mut free = HashMap::new();
    let locals = HashMap::new();
    freshen_expr_inner(expr, env, &locals, &mut free)
}
