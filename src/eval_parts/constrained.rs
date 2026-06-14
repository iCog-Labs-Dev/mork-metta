/// Constrained evaluation: evaluate expressions within nondeterministic
/// bindings.
///
/// # Semantics
///
/// When a `UserDefined` function is called with free-variable atoms as
/// arguments (atoms whose name starts with `$`), every clause is tried via
/// reversed unification and the bindings collected from each successful
/// match travel alongside the result. Those bindings let `eval_if` extend
/// the environment for template evaluation (constraint-style:
/// `(if (and (or $x True) $y) ($x $y))`).
///
/// For native functions and non-call expressions the behaviour is identical
/// to `eval` — each result is wrapped with an empty `Env`.

use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::core::eval;
use crate::eval_parts::pattern::{match_clauses, prepend_env, try_match_clause};
use crate::func::{FnTable, FunctionKind, NDet};
use crate::parser::Expr;

/// Evaluate `expr` returning (result, bindings) pairs.
pub(crate) fn eval_constrained(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Atom, Env)>, String> {
    // Free variable: return the atom (bound or self-evaluated) with no new bindings.
    if let Expr::Symbol(s) = expr {
        if s.starts_with('$') {
            let val = env.get(s).unwrap_or_else(|| Atom::sym(s));
            return Ok(vec![(val, Env::new())]);
        }
    }
    // UserDefined function call: propagate bindings through clause matching.
    if let Expr::List(items) = expr {
        if !items.is_empty() {
            if let Expr::Symbol(fname) = &items[0] {
                if !fname.starts_with('$') {
                    let arity = (items.len() - 1) as u8;
                    let args = &items[1..];
                    // Space-based dispatch for user-defined functions
                    // (Native functions handled by fallthrough to eval)
                    let mut arg_streams: Vec<Vec<(Atom, Env)>> =
                        Vec::with_capacity(args.len());
                    for arg in args {
                        arg_streams.push(eval_constrained(arg, env, funcs)?);
                    }
                    let combos = constrained_cartesian(arg_streams);
                    let mut out: Vec<(Atom, Env)> = Vec::new();
                    // Look up cached clauses — fast path.
                    let clauses: Vec<crate::func::Clause> = match funcs.fn_cache.read().unwrap()
                        .get(fname.as_str()).and_then(|inner| inner.get(&(args.len() as u8)))
                    {
                        Some(c) => c.clone(),
                        // Cache miss — try space (test code that adds atoms directly).
                        None => {
                            let mut cls: Vec<crate::func::Clause> = Vec::new();
                            let pat = crate::space::Pattern::Expr(vec![
                                crate::space::Pattern::Exact(Atom::sym("=")),
                                crate::space::Pattern::Expr(
                                    std::iter::once(crate::space::Pattern::Exact(Atom::sym(fname.as_str())))
                                        .chain((0..args.len()).map(|_| crate::space::Pattern::Any))
                                        .collect()
                                ),
                                crate::space::Pattern::Any,
                            ]);
                            let space_matches = funcs.space.read().unwrap().match_atoms(&pat);
                            for m in space_matches {
                                if let Atom::Expr(items) = &m.atom {
                                    if items.len() == 3 {
                                        if let Ok(head_expr) = crate::parser::atom_to_expr(&items[1]) {
                                            if let crate::parser::Expr::List(head_items) = &head_expr {
                                                let patterns: Vec<crate::parser::Expr> = head_items[1..].to_vec();
                                                let body = crate::parser::atom_to_expr(&items[2])
                                                    .unwrap_or_else(|_| crate::parser::Expr::Symbol(items[2].to_sexpr_string()));
                                                cls.push(crate::func::Clause { patterns, body });
                                            }
                                        }
                                    }
                                }
                            }
                            if cls.is_empty() && !out.is_empty() { return Ok(out); }
                            cls
                        }
                    };
                    for (atom_args, arg_bindings) in &combos {
                        for clause in &clauses {
                            let mut unif_env = crate::env::Env::new();
                            let mut matched = true;
                            for (pat, arg_val) in clause.patterns.iter().zip(atom_args.iter()) {
                                match crate::eval_parts::pattern::try_match_one(pat, arg_val, &unif_env, funcs) {
                                    Ok(Some(new_env)) => unif_env = new_env,
                                    _ => { matched = false; break; }
                                }
                            }
                            if !matched {
                                continue;
                            }
                            let body_env = crate::eval_parts::pattern::prepend_env(unif_env, env);
                            for (result_atom, body_bindings) in eval_constrained(&clause.body, &body_env, funcs)? {
                                let accumulated = prepend_env(body_bindings, arg_bindings);
                                out.push((result_atom, accumulated));
                            }
                        }
                    }
                    if !out.is_empty() {
                        return Ok(out);
                    }
                }
            }
        }
    }
    // Dynamic operator (closure via $var or inline lambda expr): e.g. ($f $z) or ((|-> ...) $z)
    if let Expr::List(items) = expr {
        if !items.is_empty() {
            let head = &items[0];
            // Skip if already handled above (plain non-$ symbol)
            let is_plain_fn = matches!(head, Expr::Symbol(s) if !s.starts_with('$'));
            if !is_plain_fn {
                let args = &items[1..];
                let op_atom: Option<Atom> = match head {
                    Expr::Symbol(s) => env.get(s),
                    other => eval(other, env, funcs)?.next(),
                };
                if let Some(Atom::Closure(c)) = op_atom {
                    let mut arg_streams: Vec<Vec<(Atom, Env)>> = Vec::with_capacity(args.len());
                    for arg in args {
                        arg_streams.push(eval_constrained(arg, env, funcs)?);
                    }
                    let combos = constrained_cartesian(arg_streams);
                    let mut out: Vec<(Atom, Env)> = Vec::new();
                    for (atom_args, arg_bindings) in combos {
                        if let Some(match_bindings) =
                            try_match_clause(&c.params, &atom_args, &Env::new(), funcs)?
                        {
                            let full_env = prepend_env(match_bindings.clone(), &c.env);
                            for (atom, body_bindings) in
                                eval_constrained(&c.body, &full_env, funcs)?
                            {
                                let acc = prepend_env(
                                    body_bindings,
                                    &prepend_env(match_bindings.clone(), &arg_bindings),
                                );
                                out.push((atom, acc));
                            }
                        }
                    }
                    if !out.is_empty() {
                        return Ok(out);
                    }
                }
            }
        }
    }
    // Fallback: normal eval, wrap each result with empty bindings.
    eval(expr, env, funcs).map(|ndet| ndet.map(|a| (a, Env::new())).collect())
}

/// Build the cartesian product of per-argument value lists, producing every
/// combination as a Vec<Atom>.  Used by `call_with_ref` to thread
/// nondeterminism through function calls.
pub(crate) fn cartesian_product(options: &[Vec<Atom>]) -> Vec<Vec<Atom>> {
    if options.is_empty() {
        return vec![vec![]];
    }
    let mut result = vec![vec![]];
    for opt in options {
        let mut new_result = Vec::with_capacity(result.len() * opt.len());
        for prefix in &result {
            for val in opt {
                let mut combined = prefix.clone();
                combined.push(val.clone());
                new_result.push(combined);
            }
        }
        result = new_result;
    }
    result
}

/// Build the cartesian product of per-argument result streams, accumulating bindings.
pub(crate) fn constrained_cartesian(
    streams: Vec<Vec<(Atom, Env)>>,
) -> Vec<(Vec<Atom>, Env)> {
    if streams.is_empty() {
        return vec![(vec![], Env::new())];
    }
    let mut result = vec![(vec![], Env::new())];
    for stream in &streams {
        let mut new_result = Vec::new();
        for (prefix_atoms, prefix_env) in &result {
            for (val, val_env) in stream {
                let mut atoms = prefix_atoms.clone();
                atoms.push(val.clone());
                let merged_env = prepend_env(val_env.clone(), prefix_env);
                new_result.push((atoms, merged_env));
            }
        }
        result = new_result;
    }
    result
}
