/// Core evaluation dispatch loop.
///
/// This module contains the main `eval` function, the entry point
/// `eval_scope`, function-call dispatch (`try_call_or_data`), closure
/// application (`apply_closure`), and the parallel arg-evaluation dispatch
/// (`call_with_cloned`).
///
/// # Dispatch order
///
/// 1. **Number** → single-element iterator with `Atom::Num(n)`
/// 2. **Symbol** → variable lookup (if `$` prefix) else self-evaluating symbol
/// 3. **List** → two possible interpretations:
///    a. **Function call** — first element is a special form (not evaluated),
///       a known function symbol, or evaluates to a known function name.
///       Arguments are evaluated (first result each) and passed.
///    b. **Data list** — when the first element is NOT a known function or
///       special form, the whole list is treated as data: each element is
///       evaluated and the results collected into a single `Atom::Expr`.
///
/// # Thread safety
///
/// Parallelism happens automatically inside the evaluator:
/// - `par_iter` in `call_with_cloned` (pure function arg eval)
/// - `par_iter` in `eval_data_list_par` (pure data list elements)
/// All use Rayon's global thread pool.
use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::constrained::cartesian_product;
use crate::eval_parts::data_list::{eval_data_list, eval_data_list_with_head};
use crate::eval_parts::io::{eval_import, eval_import_rs, eval_println, eval_readln};
use crate::eval_parts::pattern::match_clauses;
use crate::eval_parts::python::eval_py_call;
use crate::eval_parts::space_ops::{eval_add_atom, eval_match, eval_remove_atom, eval_transform};
use crate::eval_parts::special::{
    eval_call, eval_case, eval_chain, eval_collapse, eval_eval, eval_foldall, eval_forall, eval_if,
    eval_lambda, eval_let, eval_let_star, eval_map_atom, eval_once, eval_progn, eval_quote,
    eval_repr, eval_superpose, eval_within,
};
use crate::func::{FnTable, Function, FunctionKind, NDet};
use crate::parser::Expr;
use crate::{trace, trace_enter, trace_exit};
use std::sync::Arc;

/// Top-level entry point: evaluate an expression.
///
/// Dispatches to the active evaluation engine (see [`crate::eval_parts::cek`]):
/// the recursive tree-walk (`eval`) or the iterative CEK machine. All callers
/// that want engine-switchable evaluation must go through `eval_scope`, not
/// `eval` directly.
pub fn eval_scope(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    match crate::eval_parts::cek::current_engine() {
        crate::eval_parts::cek::Engine::Recursive => eval(expr, env, funcs),
        crate::eval_parts::cek::Engine::Cek => {
            crate::eval_parts::cek::run_as_ndet(expr, env, funcs)
        }
    }
}

/// Evaluate an expression, returning a (possibly empty) stream of results.
pub fn eval(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    trace_enter!("eval: {}", expr_to_atom(expr).to_sexpr_string());
    let result: Result<NDet, String> = match expr {
        // ---- Atoms (self-evaluating) ----
        Expr::Number(n) => {
            trace!("→ Num({})", n);
            Ok(NDet::single(Atom::Num(*n)))
        }

        Expr::Symbol(s) => {
            if s.starts_with('$') {
                let val = env.get(s).unwrap_or_else(|| Atom::sym(s));
                trace!("→ lookup ${} = {}", &s[1..], val.to_sexpr_string());
                Ok(NDet::single(val))
            } else {
                trace!("→ Sym({})", s);
                Ok(NDet::single(Atom::sym(s)))
            }
        }
        // ---- Compound forms (lists) ----
        Expr::List(items) => {
            if items.is_empty() {
                trace!("→ () = Expr([])");
                return Ok(NDet::single(Atom::Expr(vec![])));
            }

            let op = &items[0];
            let args = &items[1..];

            // ---- Special forms (operator NOT evaluated) ----
            if let Expr::Symbol(s) = op {
                match s.as_str() {
                    "if" => {
                        trace!("→ special: if");
                        return eval_if(args, env, funcs);
                    }
                    "progn" => {
                        trace!("→ special: progn");
                        return eval_progn(args, env, funcs);
                    }
                    "let" => {
                        trace!("→ special: let");
                        return eval_let(args, env, funcs);
                    }
                    "let*" => {
                        trace!("→ special: let*");
                        return eval_let_star(args, env, funcs);
                    }
                    "quote" => {
                        trace!("→ special: quote");
                        return eval_quote(args, env);
                    }
                    "call" => {
                        trace!("→ special: call");
                        return eval_call(args, env, funcs);
                    }
                    "reduce" => {
                        trace!("→ special: reduce");
                        return eval_call(args, env, funcs);
                    }
                    "eval" => {
                        trace!("→ special: eval");
                        return eval_eval(args, env, funcs);
                    }
                    "add-atom" => {
                        trace!("→ special: add-atom");
                        return eval_add_atom(args, env, funcs);
                    }
                    "transform" => {
                        trace!("→ special: transform");
                        return eval_transform(args, env, funcs);
                    }
                    "remove-atom" => {
                        trace!("→ special: remove-atom");
                        return eval_remove_atom(args, env, funcs);
                    }
                    "match" => {
                        trace!("→ special: match");
                        return eval_match(args, env, funcs);
                    }
                    "import!" => {
                        trace!("→ special: import!");
                        return eval_import(args, env, funcs);
                    }
                    "readln!" => {
                        trace!("→ special: readln!");
                        return eval_readln(args, env, funcs);
                    }
                    "println!" => {
                        trace!("→ special: println!");
                        return eval_println(args, env, funcs);
                    }
                    "superpose" => {
                        trace!("→ special: superpose");
                        return eval_superpose(args, env, funcs);
                    }
                    "collapse" => {
                        trace!("→ special: collapse");
                        return eval_collapse(args, env, funcs);
                    }
                    "chain" => {
                        trace!("→ special: chain");
                        return eval_chain(args, env, funcs);
                    }
                    "case" => {
                        trace!("→ special: case");
                        return eval_case(args, env, funcs);
                    }
                    "foldall" => {
                        trace!("→ special: foldall");
                        return eval_foldall(args, env, funcs);
                    }
                    "map-atom" => {
                        trace!("→ special: map-atom");
                        return eval_map_atom(args, env, funcs);
                    }
                    "|->" => {
                        trace!("→ special: lambda");
                        return eval_lambda(args, env);
                    }
                    "forall" => {
                        trace!("→ special: forall");
                        return eval_forall(args, env, funcs);
                    }
                    "repr" => {
                        trace!("→ special: repr");
                        return eval_repr(args, env);
                    }
                    "within" => {
                        trace!("→ special: within");
                        return eval_within(args, env, funcs);
                    }
                    "empty" => {
                        trace!("→ special: empty");
                        return Ok(NDet::stream(std::iter::empty()));
                    }
                    "once" => {
                        trace!("→ special: once");
                        return eval_once(args, env, funcs);
                    }
                    "py-call" => {
                        trace!("→ special: py-call");
                        return eval_py_call(args, env, funcs);
                    }
                    "import-rs!" => {
                        trace!("→ special: import-rs!");
                        return eval_import_rs(args, env, funcs);
                    }
                    _ => {}
                }
            }

            // ---- Function call or data list ----
            trace!("→ try_call_or_data");
            try_call_or_data(op, args, items, env, funcs)
        }
    };
    trace_exit!();
    result
}

/// Try to interpret a list as a function call.
///
/// If the first element names a known function (directly or via $variable),
/// dispatch. Otherwise evaluate as a data list: each element evaluates and
/// results are collected into a single `Atom::Expr`.
fn try_call_or_data(
    op: &Expr,
    args: &[Expr],
    all_items: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    // Helper: if a head atom is a lambda closure, apply it.
    let try_apply_lambda =
        |head: &Atom, env: &Env, args: &[Expr]| -> Option<Result<NDet, String>> {
            if let Atom::Closure(data) = head {
                return Some(apply_closure(
                    &data.params,
                    &data.body,
                    &data.env,
                    args,
                    env,
                    funcs,
                ));
            }
            None
        };

    match op {
        Expr::Symbol(s) if s.starts_with('$') => {
            let op_val = env.get(s).unwrap_or_else(|| Atom::sym(s));
            match &op_val {
                Atom::Sym(func_name) => {
                    trace!("→ $var op '{}' = '{}'", s, func_name);
                    return match funcs.get(func_name, args.len() as u8) {
                        Some(func) => call_with_cloned(&*func, func_name, args, env, funcs),
                        None => {
                            // Try space-based function dispatch before treating as data
                            if let Some(result) = try_eval_from_space(func_name, args, env, funcs)?
                            {
                                return Ok(result);
                            }
                            trace!("→ unknown symbol '{}', treating as data list", s);
                            eval_data_list(all_items, env, funcs)
                        }
                    };
                }
                _ => {
                    // Variable resolved to a non-symbol value (e.g. a lambda closure).
                    // Try to apply as a lambda first.
                    if let Some(result) = try_apply_lambda(&op_val, env, args) {
                        return result;
                    }
                }
            }
            // Fall back: re-evaluate the operator and treat the whole thing as data.
            let head = eval(op, env, funcs)?.next();
            match head {
                Some(h) => eval_data_list_with_head(h, args, env, funcs),
                None => eval_data_list(all_items, env, funcs),
            }
        }
        Expr::Symbol(s) => {
            if !s.starts_with('$') {
                return match funcs.get(s, args.len() as u8) {
                    Some(func) => call_with_cloned(&*func, s, args, env, funcs),
                    None => {
                        // Try space-based function dispatch before treating as data
                        if let Some(result) = try_eval_from_space(s, args, env, funcs)? {
                            return Ok(result);
                        }
                        trace!("→ unknown symbol '{}', treating as data list", s);
                        eval_data_list(all_items, env, funcs)
                    }
                };
            }
            eval_data_list(all_items, env, funcs)
        }
        _ => {
            // Operator is a compound expression (e.g. a lambda literal or something
            // that evaluates to a function). Evaluate it, then dispatch.
            let op_val = eval(op, env, funcs)?.next();
            match op_val {
                Some(Atom::Sym(func_name)) => {
                    match funcs.get(&func_name, args.len() as u8) {
                        Some(func) => call_with_cloned(&*func, &func_name, args, env, funcs),
                        None => {
                            // Try space-based function dispatch before treating as data
                            if let Some(result) = try_eval_from_space(&func_name, args, env, funcs)?
                            {
                                return Ok(result);
                            }
                            let head = Some(Atom::Sym(func_name));
                            eval_data_list_with_head(head.unwrap(), args, env, funcs)
                        }
                    }
                }
                Some(head) => {
                    // Check if it's a lambda closure — apply it directly.
                    if let Some(result) = try_apply_lambda(&head, env, args) {
                        return result;
                    }
                    eval_data_list_with_head(head, args, env, funcs)
                }
                None => eval_data_list(all_items, env, funcs),
            }
        }
    }
}

/// Apply a closure to a list of argument expressions.
pub(crate) fn apply_closure(
    params: &[Expr],
    body: &Expr,
    capture_env: &Env,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    if params.len() != args.len() {
        return Err(format!(
            "closure: expected {} arguments, got {}",
            params.len(),
            args.len()
        ));
    }

    // Evaluate each argument to its FULL result set and cartesian-product them,
    // so non-deterministic arguments propagate every branch (Σ over transitions)
    // instead of being truncated to the first. Deterministic args → one combo,
    // identical to the previous behavior.
    let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
    for arg in args {
        let vals: Vec<Atom> = eval(arg, env, funcs)?.collect();
        if vals.is_empty() {
            return Err("closure: argument produced no results".into());
        }
        arg_options.push(vals);
    }

    let combos = cartesian_product(&arg_options);
    let single_combo = combos.len() == 1;
    let mut streams: Vec<NDet> = Vec::new();
    for arg_vals in &combos {
        let mut match_env = Env::new();
        let mut mismatch: Option<String> = None;
        for (pat, val) in params.iter().zip(arg_vals.iter()) {
            match crate::eval_parts::pattern::try_match_one(pat, val, &match_env, funcs)? {
                Some(new_env) => match_env = new_env,
                None => {
                    mismatch = Some(format!(
                        "closure: pattern {} does not match argument {}",
                        pat.to_string(),
                        val.to_sexpr_string()
                    ));
                    break;
                }
            }
        }
        if let Some(msg) = mismatch {
            // Preserve the hard error for the deterministic single-combo case;
            // with multiple combos a non-matching branch simply contributes nothing.
            if single_combo {
                return Err(msg);
            }
            continue;
        }
        let full_env = crate::eval_parts::pattern::prepend_env(match_env, capture_env);
        streams.push(eval(body, &full_env, funcs)?);
    }
    Ok(NDet::stream(streams.into_iter().flatten()))
}

/// Try to resolve a function call from (= ...) definitions in the space.
///
/// When a symbol+arity doesn't match any native FnTable entry, we fall back
/// to querying the atom space for user-defined function definitions.
/// Each matching definition produces its instantiated body (stored `$vars`
/// already substituted) which is then evaluated.
///
/// Returns `Ok(Some(NDet))` if at least one definition was found,
/// `Ok(None)` if no matching definition exists in the space.
/// Fallback when fn_cache misses: query the space directly.
/// Needed when atoms were added to space without going through
/// the normal add-atom path (e.g. test code that adds atoms directly).
fn try_eval_from_space_fallback(
    name: &str,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<NDet>, String> {
    use crate::eval_parts::constrained::cartesian_product;

    let mut head_patterns: Vec<crate::space::Pattern> =
        vec![crate::space::Pattern::Exact(Atom::sym(name))];
    for _ in 0..args.len() {
        head_patterns.push(crate::space::Pattern::Any);
    }
    let def_pattern = crate::space::Pattern::Expr(vec![
        crate::space::Pattern::Exact(Atom::sym("=")),
        crate::space::Pattern::Expr(head_patterns),
        crate::space::Pattern::Any,
    ]);

    let matches = funcs.space.read().unwrap().match_atoms(&def_pattern);
    if matches.is_empty() {
        return Ok(None);
    }

    let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
    for arg in args {
        let mut results = eval(arg, env, funcs)?;
        let vals: Vec<Atom> = results.by_ref().collect();
        if vals.is_empty() {
            return Ok(None);
        }
        arg_options.push(vals);
    }

    let combos = cartesian_product(&arg_options);
    let mut streams: Vec<NDet> = Vec::new();

    for arg_vals in &combos {
        for m in &matches {
            let (def_head_patterns, body) = match &m.atom {
                Atom::Expr(items) if items.len() == 3 => match &items[1] {
                    Atom::Expr(head_items) if head_items.len() == args.len() + 1 => {
                        (&head_items[1..], &items[2])
                    }
                    _ => continue,
                },
                _ => continue,
            };

            let mut unif_env = crate::env::Env::new();
            let mut matched = true;
            for (head_pat, arg_val) in def_head_patterns.iter().zip(arg_vals.iter()) {
                let head_expr = crate::parser::atom_to_expr(head_pat)
                    .unwrap_or_else(|_| crate::parser::Expr::Symbol(head_pat.to_sexpr_string()));
                match crate::eval_parts::pattern::try_match_one(
                    &head_expr, arg_val, &unif_env, funcs,
                ) {
                    Ok(Some(new_env)) => unif_env = new_env,
                    _ => {
                        matched = false;
                        break;
                    }
                }
            }
            if !matched {
                continue;
            }

            let body_env = crate::eval_parts::pattern::prepend_env(unif_env, env);
            let body_expr = crate::parser::atom_to_expr(body)
                .unwrap_or_else(|_| crate::parser::Expr::Symbol(body.to_sexpr_string()));
            let mut stream = eval(&body_expr, &body_env, funcs)?;
            let results: Vec<Atom> = stream.by_ref().collect();
            if !results.is_empty() {
                streams.push(NDet::Stream(Box::new(results.into_iter())));
            }
        }
    }

    if streams.is_empty() {
        Err(format!("no matching clause for ({})", name))
    } else {
        Ok(Some(NDet::stream(streams.into_iter().flatten())))
    }
}

fn try_eval_from_space(
    name: &str,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<NDet>, String> {
    use crate::eval_parts::constrained::cartesian_product;

    // Look up cached clauses — fast path with no space lock.
    let arity = args.len() as u8;
    let clauses: Vec<crate::func::Clause> = match funcs
        .fn_cache
        .read()
        .unwrap()
        .get(name)
        .and_then(|inner| inner.get(&arity))
    {
        Some(c) => c.clone(),
        None => {
            // Cache miss — try to populate from space (e.g. test code that
            // added atoms directly). This is slower but ensures correctness.
            return try_eval_from_space_fallback(name, args, env, funcs);
        }
    };

    // Evaluate each argument to collect all result alternatives.
    let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
    for arg in args {
        let mut results = eval(arg, env, funcs)?;
        let vals: Vec<Atom> = results.by_ref().collect();
        if vals.is_empty() {
            return Ok(None);
        }
        arg_options.push(vals);
    }

    let combos = cartesian_product(&arg_options);
    let mut streams: Vec<NDet> = Vec::new();

    for arg_vals in &combos {
        for clause in &clauses {
            let mut unif_env = crate::env::Env::new();
            let mut matched = true;
            for (pat, arg_val) in clause.patterns.iter().zip(arg_vals.iter()) {
                match crate::eval_parts::pattern::try_match_one(pat, arg_val, &unif_env, funcs) {
                    Ok(Some(new_env)) => unif_env = new_env,
                    _ => {
                        matched = false;
                        break;
                    }
                }
            }
            if !matched {
                continue;
            }

            let body_env = crate::eval_parts::pattern::prepend_env(unif_env, env);
            streams.push(eval(&clause.body, &body_env, funcs)?);
        }
    }

    if streams.is_empty() {
        Err(format!("no matching clause for ({})", name))
    } else {
        Ok(Some(NDet::stream(streams.into_iter().flatten())))
    }
}

pub(crate) fn call_with_cloned(
    func: &Function,
    op_name: &str,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    let name = func.name.clone();
    let native_func: Option<
        Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>,
    > = match &func.kind {
        FunctionKind::Native { func: f } => Some(Arc::clone(f)),
    };
    trace_enter!("call: {} ({} args)", name, args.len());

    // Parallel arg eval is safe only when the ARGUMENT expressions are
    // space-free pure (no space access, no IO) — then the branches share only
    // immutable state and cannot race. Purity is sound and self-evolution-stable
    // (native flags + definition-time user-fn analysis). rayon's work-stealing
    // bounds nesting, so no global fork throttle is needed; result order is
    // preserved by the indexed collect, so output is fully reproducible.
    let parallel = crate::eval_parts::data_list::worth_parallel(args)
        && args
            .iter()
            .all(|a| crate::eval_parts::data_list::is_pure_expr(a, funcs));
    let arg_options: Vec<Vec<Atom>> = if parallel {
        use rayon::prelude::*;
        let results: Vec<Result<Vec<Atom>, String>> = args
            .par_iter()
            .map(|arg| {
                let mut results = eval(arg, env, funcs)?;
                let vals: Vec<Atom> = results.by_ref().collect();
                if vals.is_empty() {
                    Err(format!("{}: argument produced no results", name))
                } else {
                    Ok(vals)
                }
            })
            .collect();
        let mut arg_options = Vec::with_capacity(args.len());
        for r in results {
            arg_options.push(r?);
        }
        arg_options
    } else {
        let mut arg_options = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            let mut results = eval(arg, env, funcs)?;
            let vals: Vec<Atom> = results.by_ref().collect();
            if vals.is_empty() {
                return Err(format!("{}: argument {} produced no results", name, i + 1));
            }
            arg_options.push(vals);
        }
        arg_options
    };

    if let Some(f) = native_func {
        let cartesian = cartesian_product(&arg_options);
        let mut results = Vec::new();
        let mut last_err: Option<String> = None;
        for args_slice in cartesian {
            match f(&args_slice, funcs) {
                Ok(mut nd) => {
                    while let Some(a) = nd.next() {
                        results.push(a);
                    }
                }
                Err(e) => {
                    last_err = Some(e);
                }
            }
        }
        if results.is_empty() {
            if let Some(e) = last_err {
                trace_exit!();
                return Err(e);
            }
        }
        trace_exit!();
        return Ok(NDet::Stream(Box::new(results.into_iter())));
    }

    // No native function found — shouldn't reach here since call_with_cloned
    // is only called when funcs.get() returns Some(...)
    trace_exit!();
    Err(format!(
        "{}: internal error — missing native function",
        op_name
    ))
}

/// Convert an `Expr` to an `Atom` for tracing output.
fn expr_to_atom(expr: &Expr) -> Atom {
    match expr {
        Expr::Number(n) => Atom::Num(*n),
        Expr::Symbol(s) => Atom::sym(s),
        Expr::List(items) => {
            let atoms: Vec<Atom> = items.iter().map(expr_to_atom).collect();
            Atom::Expr(atoms)
        }
    }
}

// ========================================================================
// Phase 2: Integration with State Machine
// ========================================================================

pub(crate) fn eval_in_context(
    atom: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<Atom>, String> {
    let expr = crate::parser::atom_to_expr(atom).unwrap_or_else(|_| {
        // If conversion fails, treat the atom as a symbol fallback.
        Expr::Symbol(atom.to_sexpr_string())
    });

    let mut results = Vec::new();
    let mut stream = eval_scope(&expr, env, funcs)?;
    while let Some(result) = stream.next() {
        results.push(result);
    }

    Ok(results)
}

pub fn eval_with_state(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    cost_budget: Option<i64>,
) -> Result<(NDet, Option<i64>), String> {
    use crate::eval_parts::machine::{MachineState, Transition};

    // Ordinary runtime evaluation still runs through the active evaluator so
    // user-function calls preserve eager argument evaluation and existing
    // special-form behavior. Machine-native surface forms such as transform,
    // add-atom, and remove-atom are routed through transitions inside eval().
    let mut budget = cost_budget;
    let produced: Vec<Atom> = match crate::eval_parts::cek::current_engine() {
        crate::eval_parts::cek::Engine::Cek => {
            crate::eval_parts::cek::run_budgeted(expr, env, funcs, &mut budget)?
        }
        crate::eval_parts::cek::Engine::Recursive => eval(expr, env, funcs)?.collect(),
    };

    let mut state = MachineState::new(budget);
    for r in produced {
        state.workspace.push_back(r);
    }

    while !state.workspace.is_empty() {
        state.step(Transition::Output, env, funcs)?;
    }

    let remaining_budget = state.cost_budget;
    let ndet = NDet::stream(state.output.into_iter());
    Ok((ndet, remaining_budget))
}
