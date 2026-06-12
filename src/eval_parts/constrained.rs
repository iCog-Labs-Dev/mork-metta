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
                    if let Some(func) = funcs.get(fname, arity) {
                        if let FunctionKind::UserDefined { clauses } = &func.kind {
                            // Evaluate each arg with constraint awareness.
                            let mut arg_streams: Vec<Vec<(Atom, Env)>> =
                                Vec::with_capacity(args.len());
                            for arg in args {
                                arg_streams.push(eval_constrained(arg, env, funcs)?);
                            }
                            let combos = constrained_cartesian(arg_streams);
                            let mut out: Vec<(Atom, Env)> = Vec::new();
                            for (atom_args, arg_bindings) in &combos {
                                // Env::new() isolates new bindings for accumulation.
                                for (clause_bindings, clause) in
                                    match_clauses(&clauses, atom_args, &Env::new(), funcs)?
                                {
                                    let full_env = prepend_env(clause_bindings.clone(), env);
                                    for (atom, body_bindings) in
                                        eval_constrained(&clause.body, &full_env, funcs)?
                                    {
                                        let accumulated = prepend_env(
                                            body_bindings,
                                            &prepend_env(clause_bindings.clone(), arg_bindings),
                                        );
                                        out.push((atom, accumulated));
                                    }
                                }
                            }
                            if !out.is_empty() {
                                return Ok(out);
                            }
                            // No clause matched — fall through to eval for error message.
                        }
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
