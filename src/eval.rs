/// Tree-walking evaluator for MeTTa with nondeterminism support.
///
/// Evaluates an `Expr` in a given environment and function table, returning
/// an `NDet` iterator — a lazy stream of `Atom` results.
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
///       This matches PeTTa semantics where `(1 2 3)` produces one list
///       value `[1, 2, 3]`, not three separate results.
///
/// Empty list `()` evaluates to the empty list value `Expr([])` (a single result).
/// In PeTTa, `()` is a valid term — the empty list — not "no results".
/// The "no results" case occurs only when a nondeterministic stream
/// genuinely produces no bindings (e.g., `(superpose ())` has 0 elements).
///
/// # PeTTa reference
///
/// The "data list" rule comes from PeTTa's `translator.pl` smart dispatch:
/// when the head is not a registered fun/1, the list returns as data.
/// Elements ARE evaluated in our runtime (unlike PeTTa's compile-time),
/// so nested function calls inside a data list still execute.
///
/// # Special forms
///
/// | Form | Semantics |
/// |------|-----------|
/// | `(if cond then else)` | Evaluate cond; if truthy, eval then, else eval else |
/// | `(progn e1 e2 ...)` | Evaluate each in sequence, return last form's stream |
/// | `(let $var value body)` | Bind `$var` to each value from `value`, eval body per binding |
/// | `(let* (($x a) ($y b)) body)` | Sequential `let`; later bindings see earlier ones |
/// | `(quote expr)` | Return `expr` as data (Atom) without evaluating |
/// | `(eval expr)` | Evaluate `expr`, convert result to code, evaluate again |
/// | `(superpose expr)` | Spread elements of expr (list or single atom) as nondeterministic stream |
/// | `(collapse expr)` | Collect all results of `expr` into a single list atom |
///
/// # Assumptions
/// - Numbers and plain (non-`$`) symbols are self-evaluating.
/// - `$`-prefixed symbols look up in the environment.
/// - If the first element of a list symbolically names a known function
///   (including after evaluating a `$` variable), it is a function call.
///   Otherwise the list is a data list: elements are evaluated and collected
///   into a single `Atom::Expr`.
/// - Truthiness: `Num(0)` and empty `Sym("")` are false; all else is true.
/// - Function arguments are deterministic: only the first result of each
///   argument evaluation is used.
use std::cell::Ref;
use crate::atom::Atom;
use crate::env::Env;
use crate::func::{Clause, FnTable, Function, FunctionKind, NDet};
use crate::parser::{atom_to_expr, expr_to_atom, parse_forms, Expr, TopForm};
use crate::space::Pattern;
use std::path::PathBuf;
use std::sync::Arc;
use crate::{trace, trace_enter, trace_exit};
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
                // Empty list () is the empty list value (like nil/null in PeTTa).
                // PeTTa reference: () is a valid term that evaluates to itself.
                trace!("→ () = Expr([])");
                return Ok(NDet::single(Atom::Expr(vec![])));
            }

            let op = &items[0];
            let args = &items[1..];

            // ---- Special forms (operator NOT evaluated) ----
            if let Expr::Symbol(s) = op {
                match s.as_str() {
                    "if" => { trace!("→ special: if"); return eval_if(args, env, funcs); }
                    "progn" => { trace!("→ special: progn"); return eval_progn(args, env, funcs); }
                    "let" => { trace!("→ special: let"); return eval_let(args, env, funcs); }
                    "let*" => { trace!("→ special: let*"); return eval_let_star(args, env, funcs); }
                    "quote" => { trace!("→ special: quote"); return eval_quote(args, env); }
                    "call" => { trace!("→ special: call"); return eval_call(args, env, funcs); }
                    "reduce" => { trace!("→ special: reduce"); return eval_call(args, env, funcs); }
                    "eval" => { trace!("→ special: eval"); return eval_eval(args, env, funcs); }
                    "add-atom" => { trace!("→ special: add-atom"); return eval_add_atom(args, env, funcs); }
                    "remove-atom" => { trace!("→ special: remove-atom"); return eval_remove_atom(args, env, funcs); }
                    "match" => { trace!("→ special: match"); return eval_match(args, env, funcs); }
                    "import!" => { trace!("→ special: import!"); return eval_import(args, env, funcs); }
                    "readln!" => { trace!("→ special: readln!"); return eval_readln(args, env, funcs); }
                    "println!" => { trace!("→ special: println!"); return eval_println(args, env, funcs); }
                    "superpose" => { trace!("→ special: superpose"); return eval_superpose(args, env, funcs); }
                    "collapse" => { trace!("→ special: collapse"); return eval_collapse(args, env, funcs); }
                    "chain" => { trace!("→ special: chain"); return eval_chain(args, env, funcs); }
                    "case" => { trace!("→ special: case"); return eval_case(args, env, funcs); }
                    "foldall" => { trace!("→ special: foldall"); return eval_foldall(args, env, funcs); }
                    "map-atom" => { trace!("→ special: map-atom"); return eval_map_atom(args, env, funcs); }
                    "|->" => { trace!("→ special: lambda"); return eval_lambda(args, env); }
                    "forall" => { trace!("→ special: forall"); return eval_forall(args, env, funcs); }
                    // empty produces no results (Prolog fail / empty nondeterminism)
                    "empty" => { trace!("→ special: empty"); return Ok(NDet::stream(std::iter::empty())); }
                    "py-call" => { trace!("→ special: py-call"); return eval_py_call(args, env, funcs); }
                    "import-rs!" => { trace!("→ special: import-rs!"); return eval_import_rs(args, env, funcs); }
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
    // Case 1: plain (non-$) symbol — single get_ref lookup decides call vs data.
    // No double-lookup: the Ref from get_ref is passed directly into call_with_ref.
    if let Expr::Symbol(s) = op {
        if !s.starts_with('$') {
            // SAFETY: args.len() is the number of parsed function arguments —
            // never exceeds practical limits (<10 in real usage). The cast to
            // u8 is safe because no MeTTa function has >255 args.
            return match funcs.get_ref(s, args.len() as u8) {
                Some(func_ref) => call_with_ref(func_ref, s, args, env, funcs),
                None => {
                    trace!("→ unknown symbol '{}', treating as data list", s);
                    eval_data_list(all_items, env, funcs)
                }
            };
        }
    }

    // Case 2: $variable or expression (number/nested list).
    // Evaluate the operator; if it's a known function name, call.
    let mut op_results = eval(op, env, funcs)?;
    let op_val = match op_results.next() {
        Some(a) => a,
        // Head produced no results — same error the data-list path would hit,
        // but without re-running the head's side effects.
        None => return Err("expression produced no results in data list".into()),
    };
    if let Atom::Sym(fname) = &op_val {
        // SAFETY: args.len() is small — see note above.
        if let Some(func_ref) = funcs.get_ref(fname, args.len() as u8) {
            return call_with_ref(func_ref, fname, args, env, funcs);
        }
    }
    // Case 3: closure application — operator evaluated to a Closure.
    if let Atom::Closure(c) = &op_val {
        return apply_closure(&c.params, &c.body, &c.env, args, env, funcs);
    }
    // Fallback: data list — reuse the already-evaluated head so side-effecting
    // operators (add-atom, println!, ...) don't run twice.
    trace!("→ fallback: data list");
    eval_data_list_with_head(op_val, args, env, funcs)
}
/// Apply a closure to a list of argument expressions.
///
/// 1. Evaluate each argument (first result) to get concrete values.
/// 2. Match the values against the closure's parameter patterns using
///    `try_match_clause` semantics.
/// 3. Evaluate the closure's body in the captured env extended with bindings.
fn apply_closure(
    params: &[Expr],
    body: &Expr,
    capture_env: &Env,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    trace_enter!("apply_closure: {} params, {} args", params.len(), args.len());
    // Evaluate arguments (first result of each)
    let mut arg_vals = Vec::with_capacity(args.len());
    for (i, arg) in args.iter().enumerate() {
        let mut results = eval(arg, env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("closure: argument {} produced no results", i + 1)
        })?;
        arg_vals.push(val);
    }
    #[cfg(feature = "trace")]
    let arg_strs: Vec<String> = arg_vals.iter().map(|a| a.to_sexpr_string()).collect();
    trace!("closure args: [{}]", arg_strs.join(", "));
    // Match args against params
    match try_match_clause(params, &arg_vals, capture_env, funcs)? {
        Some(match_env) => {
            trace!("closure params matched, evaluating body");
            eval(body, &match_env, funcs)
        }
        None => Err(format!(
            "closure: params do not match args: ({}) vs [{}]",
            params.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(" "),
            arg_vals.iter().map(|a| a.to_sexpr_string()).collect::<Vec<_>>().join(", ")
        )),
    }
}

/// Dispatch a function call using a pre-retrieved reference — zero extra HashMap lookup.
///
/// Holding `func: Ref<'_, Function>` while evaluating args and body is safe:
/// all concurrent borrows of `funcs.map` via `get_ref` are shared (immutable),
/// and `borrow_mut` on `funcs.map` only occurs during initialization (add_clause /
/// insert_native), never during eval.
fn call_with_ref(
    func: Ref<'_, Function>,
    op_name: &str,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    // Clone necessary data out of the Ref BEFORE evaluating args/body, because
    // body evaluation may trigger add_clause/remove_clause which borrow_mut() on
    // funcs.map — would panic if the Ref still holds an immutable borrow.
    let name = func.name.clone();
    let is_native = matches!(&func.kind, FunctionKind::Native { .. });
    let clauses: Vec<Clause> = match &func.kind {
        FunctionKind::UserDefined { clauses } => clauses.clone(),
        FunctionKind::Native { .. } => vec![],
    };
    let native_func: Option<Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + 'static>> = match &func.kind {
        FunctionKind::Native { func: f } => Some(Arc::clone(f)),
        FunctionKind::UserDefined { .. } => None,
    };
    drop(func); // Release the RefCell borrow before any recursive eval calls.
    trace_enter!("call: {} ({} args)", name, args.len());
    // Collect ALL results from each arg, don't truncate to first.
    // Nondeterminism threads through function calls: if an arg produces
    // multiple values (e.g. (g $z) → [2,3]), the function is called with
    // every combination (cartesian product).  This matches PeTTa semantics
    // where backtracking through args generates all solutions.
    let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(args.len());
    for (i, arg) in args.iter().enumerate() {
        let mut results = eval(arg, env, funcs)?;
        let vals: Vec<Atom> = results.collect();
        if vals.is_empty() {
            return Err(format!(
                "{}: argument {} produced no results",
                name, i + 1
            ));
        }
        arg_options.push(vals);
    }
    // Compute cartesian product of arg values
    #[cfg(feature = "trace")]
    {
        let opt_strs: Vec<String> = arg_options.iter()
            .map(|opts| format!("[{}]", opts.iter().map(|a| a.to_sexpr_string()).collect::<Vec<_>>().join(", ")))
            .collect();
        trace!("{} arg options: [{}]", name, opt_strs.join(", "));
    }
    let cartesian = cartesian_product(&arg_options);
    if is_native {
        if let Some(f) = native_func {
            let mut results = Vec::new();
            let mut last_err: Option<String> = None;
            for args_slice in cartesian {
                match f(&args_slice, funcs) {
                    Ok(mut nd) => {
                        while let Some(a) = nd.next() {
                            results.push(a);
                        }
                    }
                    Err(e) => { last_err = Some(e); }
                }
            }
            // If every combination failed, propagate the error.
            // If at least one succeeded, silently skip errors (matches
            // PeTTa semantics where failing branches are discarded).
            if results.is_empty() {
                if let Some(e) = last_err {
                    trace_exit!();
                    return Err(e);
                }
            }
            trace_exit!();
            return Ok(NDet::Stream(Box::new(results.into_iter())));
        }
    }
    // UserDefined: for each combination of arg values, try each clause
    let mut streams: Vec<NDet> = Vec::new();
    for arg_vals in &cartesian {
        for (new_env, clause) in match_clauses(&clauses, arg_vals, env, funcs)? {
            streams.push(eval(&clause.body, &new_env, funcs)?);
        }
    }
    if streams.is_empty() {
        // Build helpful error message from the first arg-option (all should have same arity)
        let example: Vec<String> = arg_options.iter()
            .filter_map(|opts| opts.first())
            .map(|a| a.to_sexpr_string())
            .collect();
        return Err(format!(
            "{}: no matching clause for args [{}]",
            name,
            example.join(", ")
        ));
    }
    trace_exit!();
    Ok(NDet::stream(streams.into_iter().flatten()))
}
// ========================================================================
// Pattern matching for multi-clause functions
// ========================================================================
/// Try to match argument atoms against a clause's patterns.
///
/// Uses a fresh environment for pattern matching (so outer bindings don't
/// interfere with variable capture in recursive calls). On success, extends
/// the calling `env` with the matched bindings.
///
/// Returns `Some(env)` with the extended environment if the pattern matches,
/// or `None` if this clause doesn't match (try the next one).
///
/// # Errors
/// Returns `Err` only on genuine errors (not on pattern mismatch).
fn try_match_clause(
    patterns: &[Expr],
    args: &[Atom],
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    if patterns.len() != args.len() {
        return Ok(None);
    }
    // Use a fresh env for pattern matching so outer bindings don't interfere
    // with variable capture in recursive calls (e.g., fib($N) called with
    // outer $N=30 should match $N=29, not fail).
    let mut match_env = Env::new();
    for (pat, arg) in patterns.iter().zip(args.iter()) {
        match try_match_one(pat, arg, &match_env, funcs)? {
            Some(new_env) => match_env = new_env,
            None => return Ok(None),
        }
    }
    // Splice match_env (built on Empty) onto the calling env without converting
    // to Vec<(String, Atom)> — avoids Arc<str>→String→Arc<str> round-trips.
    Ok(Some(prepend_env(match_env, env)))
}

/// Walk `match_env` (a chain built on top of Env::Empty) and replace the
/// Empty terminus with `base`, merging the two chains without any String
/// allocations — Arc<str> name references are reused as-is.
fn prepend_env(match_env: Env, base: &Env) -> Env {
    match match_env {
        Env::Empty => base.clone(),
        Env::Cons { name, value, next } => Env::Cons {
            name,
            value,
            next: Box::new(prepend_env(*next, base)),
        },
    }
}

/// Match a single pattern against a single atom.
///
/// Pattern kinds:
/// - `$var` (symbol starting with `$`): binds to the atom, or checks
///   equality if already bound (non-linear patterns).
/// - `Num(n)`: matches only `Atom::Num(n)`.
/// - `Sym(s)`: matches only `Atom::Sym(t)` where `s == t`.
/// - `List(items)`: structural match — recursively matches each element
fn try_match_one(
    pattern: &Expr,
    atom: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Env>, String> {
    match pattern {
        Expr::Symbol(s) if s.starts_with('$') => {
            // Variable pattern: bind if unbound, check equality if bound
            match env.get(s) {
                Some(bound) if &bound != atom => Ok(None),
                _ => Ok(Some(env.extend(s, atom.clone()))),
            }
        }
        Expr::Number(n) => match atom {
            Atom::Num(m) if n == m => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal number.
            Atom::Sym(s) if s.starts_with('$') => Ok(Some(env.extend(s, Atom::Num(*n)))),
            _ => Ok(None),
        },
        Expr::Symbol(s) => match atom {
            // Normalize through Atom::sym() so "True"/"False" patterns match lowercase atoms.
            Atom::Sym(t) if Atom::sym(s) == Atom::Sym(t.clone()) => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal symbol.
            Atom::Sym(v) if v.starts_with('$') => Ok(Some(env.extend(v, Atom::sym(s)))),
            _ => Ok(None),
        },
        Expr::List(items) => match atom {
            Atom::Expr(elems) => {
                if items.len() != elems.len() {
                    return Ok(None);
                }
                let mut current = env.clone();
                for (pat, arg) in items.iter().zip(elems.iter()) {
                    match try_match_one(pat, arg, &current, funcs)? {
                        Some(new_env) => current = new_env,
                        None => return Ok(None),
                    }
                }
                Ok(Some(current))
            }
            // Free variable: evaluate the List pattern as code (computation
            // in pattern, e.g. `(if (== $x 2) 43 44)`) and bind the result.
            Atom::Sym(s) if s.starts_with('$') => {
                let expr = Expr::List(items.clone());
                match eval(&expr, env, funcs) {
                    Ok(mut results) => match results.next() {
                        Some(val) => Ok(Some(env.extend(s, val))),
                        None => Ok(None),
                    },
                    Err(_) => Ok(None),
                }
            }
            _ => Ok(None),
        },
    }
}

/// Try every clause against `arg_vals`, returning `(match_env, &Clause)` for
/// each match.  This is the single call-site for `try_match_clause` across
/// both `call_with_ref` and `eval_constrained`, ensuring the two dispatch paths
/// can never diverge in their clause-selection logic.
///
/// `base_env` controls what outer variables are visible during matching:
/// - pass the calling `env` in `call_with_ref` (outer bindings in scope),
/// - pass `&Env::new()` in `eval_constrained` (isolates new bindings for accumulation).
fn match_clauses<'c>(
    clauses: &'c [Clause],
    arg_vals: &[Atom],
    base_env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Env, &'c Clause)>, String> {
    let mut matched = Vec::new();
    for clause in clauses {
        if let Some(env) = try_match_clause(&clause.patterns, arg_vals, base_env, funcs)? {
            matched.push((env, clause));
        }
    }
    Ok(matched)
}

/// Evaluate a list as data: each element is evaluated and collected into a
/// single `Atom::Expr`. This replaces the old "tuple" semantics.
///
/// PeTTa reference: when the head is not a registered fun/1, the list is
/// data — `Out = [HV|AVs]`. In our runtime each element IS evaluated
/// (including nested function calls), then collected into one list atom.
fn eval_data_list(items: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let mut atoms = Vec::with_capacity(items.len());
    for item in items {
        atoms.push(eval_data_item(item, env, funcs)?);
    }
    Ok(NDet::single(Atom::Expr(atoms)))
}

/// Like `eval_data_list`, but the head element was already evaluated by the
/// caller (operator-position dispatch in `try_call_or_data`). Reusing that
/// value instead of re-evaluating prevents side-effecting heads
/// (e.g. add-atom, println!) from running twice.
fn eval_data_list_with_head(
    head: Atom,
    rest: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    let mut atoms = Vec::with_capacity(rest.len() + 1);
    atoms.push(head);
    for item in rest {
        atoms.push(eval_data_item(item, env, funcs)?);
    }
    Ok(NDet::single(Atom::Expr(atoms)))
}

/// Evaluate one element of a data list to an Atom (first result).
fn eval_data_item(item: &Expr, env: &Env, funcs: &FnTable) -> Result<Atom, String> {
    match item {
        Expr::Number(n) => Ok(Atom::Num(*n)),
        Expr::Symbol(s) => {
            if s.starts_with('$') {
                // PeTTa: unbound $vars in a data list stay as Prolog variables
                // (structural holes). Pattern matching in let/try_match_one
                // then binds them via computation-in-pattern or direct unification.
                Ok(env.get(s).unwrap_or_else(|| Atom::sym(s)))
            } else {
                Ok(Atom::sym(s))
            }
        }
        Expr::List(inner) => {
            if inner.is_empty() {
                Ok(Atom::Expr(vec![]))
            } else {
                eval(item, env, funcs)?
                    .next()
                    .ok_or_else(|| "expression produced no results in data list".into())
            }
        }
    }
}

// ========================================================================
// Special form evaluators
// ========================================================================

/// Evaluate `expr` returning (result, bindings) pairs.
///
/// When a UserDefined function is called with free-variable atoms as arguments
/// (atoms whose name starts with `$`), every clause is tried via reversed
/// unification and the bindings collected from each successful match travel
/// alongside the result. Those bindings let `eval_if` extend the environment
/// for template evaluation (constraint-style: `(if (and (or $x True) $y) ($x $y))`).
///
/// For native functions and non-call expressions the behaviour is identical to
/// `eval` — each result is wrapped with an empty `Env`.
fn eval_constrained(
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
                        if let FunctionKind::UserDefined { clauses } = func.kind {
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
fn cartesian_product(options: &[Vec<Atom>]) -> Vec<Vec<Atom>> {
    let mut result: Vec<Vec<Atom>> = vec![vec![]];
    for opts in options {
        let mut next: Vec<Vec<Atom>> = Vec::with_capacity(result.len() * opts.len());
        for prefix in &result {
            for val in opts {
                let mut combined = prefix.clone();
                combined.push(val.clone());
                next.push(combined);
            }
        }
        result = next;
    }
    result
}

/// Build the cartesian product of per-argument result streams, accumulating bindings.
fn constrained_cartesian(streams: Vec<Vec<(Atom, Env)>>) -> Vec<(Vec<Atom>, Env)> {
    let mut result: Vec<(Vec<Atom>, Env)> = vec![(vec![], Env::new())];
    for stream in streams {
        let mut next: Vec<(Vec<Atom>, Env)> = Vec::new();
        for (atoms, env_acc) in result {
            for (atom, bindings) in &stream {
                let mut new_atoms = atoms.clone();
                new_atoms.push(atom.clone());
                let new_env = prepend_env(bindings.clone(), &env_acc);
                next.push((new_atoms, new_env));
            }
        }
        result = next;
    }
    result
}

/// Evaluate `(if cond then else)`.
fn eval_if(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() < 2 || args.len() > 3 {
        return Err(format!(
            "if: expected 2 or 3 args, got {}",
            args.len()
        ));
    }
    // Use constraint-aware evaluation for the condition so free-variable bindings
    // (e.g. $x→True from clause matching) are threaded into the template.
    let mut out: Vec<Atom> = Vec::new();
    let mut had_bindings = false;
    for (cond, cond_bindings) in eval_constrained(&args[0], env, funcs)? {
        if !matches!(cond_bindings, crate::env::Env::Empty) {
            had_bindings = true;
        }
        if cond.is_truthy() {
            let then_env = prepend_env(cond_bindings, env);
            out.extend(eval(&args[1], &then_env, funcs)?);
        } else if let Some(else_expr) = args.get(2) {
            out.extend(eval(else_expr, env, funcs)?);
        }
        // 2-arg form: false condition contributes nothing
    }
    Ok(match out.len() {
        0 => NDet::stream(std::iter::empty()),
        1 => NDet::single(out.remove(0)),
        // Constraint-solving produced multiple solutions (bindings were non-empty):
        // collect into a single list atom so (test (if cond tmpl) ((s1) (s2))) works.
        // Non-det condition (superpose etc.) with empty bindings: stream results.
        _ if had_bindings => NDet::single(Atom::Expr(out)),
        _ => NDet::stream(out.into_iter()),
    })
}

/// Evaluate `(progn e1 e2 ...)` — sequence.
/// In PeTTa, `let` variables leak into the rest of the progn. We replicate this
/// by AST-rewriting the rest of the progn into the let body.
fn eval_progn(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.is_empty() {
        return Err("progn: expected at least one form".into());
    }

    let mut last: Option<NDet> = None;
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];

        // Rewrite (let pat val body) followed by e_rest...
        // into (let pat val (progn body e_rest...))
        if let Expr::List(items) = arg {
            if items.len() == 4 && items[0] == Expr::Symbol("let".to_string()) {
                if i + 1 < args.len() {
                    let pat = items[1].clone();
                    let val = items[2].clone();
                    let body = &items[3];
                    let mut new_progn_args = vec![body.clone()];
                    new_progn_args.extend_from_slice(&args[i+1..]);
                    let new_progn = Expr::List(
                        vec![Expr::Symbol("progn".to_string())]
                            .into_iter()
                            .chain(new_progn_args)
                            .collect()
                    );
                    let new_let = Expr::List(vec![
                        Expr::Symbol("let".to_string()),
                        pat,
                        val,
                        new_progn,
                    ]);
                    last = Some(eval(&new_let, env, funcs)?);
                    break; // The rest of the forms are now in the `let` body
                }
            } else if items.len() == 3 && items[0] == Expr::Symbol("let*".to_string()) {
                if i + 1 < args.len() {
                    let bindings = items[1].clone();
                    let body = &items[2];
                    let mut new_progn_args = vec![body.clone()];
                    new_progn_args.extend_from_slice(&args[i+1..]);
                    let new_progn = Expr::List(
                        vec![Expr::Symbol("progn".to_string())]
                            .into_iter()
                            .chain(new_progn_args)
                            .collect()
                    );
                    let new_let = Expr::List(vec![
                        Expr::Symbol("let*".to_string()),
                        bindings,
                        new_progn,
                    ]);
                    last = Some(eval(&new_let, env, funcs)?);
                    break;
                }
            } else if items.len() == 4 && items[0] == Expr::Symbol("match".to_string()) {
                // Wrap subsequent forms into a let block that binds the output of match.
                // e.g. (match space pat result) e_rest...
                // => (let result (match space pat result) (progn e_rest...))
                // But only if `result` acts as a pattern (usually just a variable like $x).
                if i + 1 < args.len() {
                    if let Expr::Symbol(s) = &items[3] {
                        if s.starts_with('$') {
                            let result_var = items[3].clone();
                            let mut new_progn_args = vec![];
                            new_progn_args.extend_from_slice(&args[i+1..]);
                            let new_progn = Expr::List(
                                vec![Expr::Symbol("progn".to_string())]
                                    .into_iter()
                                    .chain(new_progn_args)
                                    .collect()
                            );
                            let new_let = Expr::List(vec![
                                Expr::Symbol("let".to_string()),
                                result_var,
                                arg.clone(), // The match!
                                new_progn,
                            ]);
                            last = Some(eval(&new_let, env, funcs)?);
                            break;
                        }
                    }
                }
            }
        }

        last = Some(eval(arg, env, funcs)?);
        i += 1;
    }
    last.ok_or_else(|| "progn: internal — no forms after empty check".into())
}

/// Evaluate `(let pattern value body)` — nondeterministic pattern matching bind.
///
/// Evaluates `value` to produce a stream of atoms. For each atom, tries to
/// match `pattern` against it. On match, extends the environment with the
/// bindings and evaluates `body`. On mismatch, that branch produces no
/// results (empty stream contribution).
///
/// Pattern syntax (same as multi-clause `try_match_one`):
/// - `$var` — bind to value, or check equality if already bound by earlier
///   pattern elements (non-linear patterns)
/// - `Num(n)` — match only `Atom::Num(n)`
/// - `Sym(s)` — match only `Atom::Sym(s)` (non-`$` symbols are literal)
/// - `(pat1 pat2 ...)` — destructuring match against `Atom::Expr`
fn eval_let(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "let: expected (pattern value body), got {} args",
            args.len()
        ));
    }
    let pattern = &args[0];
    // PeTTa: translate_expr(Val, Gv, V) — always evaluate the value expression.
    let values: Vec<Atom> = eval(&args[1], env, funcs)?.collect();
    let streams: Vec<NDet> = values
        .into_iter()
        .filter_map(|v| {
            // Fresh match env prevents outer variable capture
            let match_env = try_match_one(pattern, &v, &Env::new(), funcs).ok()??;
            let new_env = prepend_env(match_env, env);
            // REASON: body eval failure in nondet stream is skipped,
            // not propagated — matches PeTTa's backtracking semantics.
            match eval(&args[2], &new_env, funcs) {
                Ok(res) => Some(res),
                Err(e) => {
                    eprintln!("DEBUG eval_let error: {}", e);
                    None
                }
            }
        })
        .collect();
    Ok(NDet::stream(streams.into_iter().flatten()))
}

/// Evaluate `(let* ((pat val) (pat2 val2) ...) body)` — sequential pattern let.
///
/// Evaluates each value in order. For each value, matches the corresponding
/// pattern using the same semantics as `try_match_one`. Later bindings see
/// variables bound by earlier patterns. If any pattern fails to match the
/// value, returns an error (deterministic binding).
fn eval_let_star(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "let*: expected ((bindings) body), got {} args",
            args.len()
        ));
    }
    let bindings = match &args[0] {
        Expr::List(items) => items,
        _ => {
            return Err(
                "let*: first arg must be a list of (pattern val) pairs".into(),
            )
        }
    };
    let mut current_env = env.clone();
    for pair in bindings {
        match pair {
            Expr::List(p) if p.len() == 2 => {
                let pattern = &p[0];
                // PeTTa: letstar_to_rec_let expands to nested let, which always evaluates.
                let mut val_results = eval(&p[1], &current_env, funcs)?;
                let val = val_results.next().ok_or_else(|| {
                    format!("let*: binding {} produced no value", pattern.to_string())
                })?;
                // Fresh match env prevents outer variable capture
                let match_env = try_match_one(pattern, &val, &Env::new(), funcs)?
                    .ok_or_else(|| {
                        format!("let*: pattern does not match value: {} vs {}",
                            pattern.to_string(), val.to_sexpr_string())
                    })?;
                current_env = prepend_env(match_env, &current_env);
            }
            _ => {
                return Err("let*: each binding must be a list (pattern val)".into())
            }
        }
    }
    eval(&args[1], &current_env, funcs)
}
/// Evaluate `(quote expr)` — return expression as data, substituting bound `$vars`.
///
/// PeTTa: `Out = Expr` where Expr is the raw Prolog term. Bound Prolog variables
/// are already unified, so `(quote $x)` where $x=10 returns 10, not the symbol "$x".
/// We replicate this by substituting env-bound `$vars` before converting to atom.
fn eval_quote(args: &[Expr], env: &Env) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("quote: expected 1 arg, got {}", args.len()));
    }
    let atom = subst_and_atomize(&args[0], env);
    Ok(NDet::single(atom))
}

/// Convert an `Expr` to an `Atom`, substituting bound `$vars` from `env`.
/// Unbound `$vars` are left as `Atom::Sym("$name")`.
fn subst_and_atomize(expr: &Expr, env: &Env) -> Atom {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            env.get(s).unwrap_or_else(|| Atom::sym(s))
        }
        Expr::List(items) => Atom::Expr(items.iter().map(|e| subst_and_atomize(e, env)).collect()),
        Expr::Number(n) => Atom::Num(*n),
        Expr::Symbol(s) => Atom::sym(s),
    }
}

/// Substitute bound variables in an Expr, keeping pattern structure intact.
/// Converts Atom values back to Expr for use in patterns.
fn subst_expr_vars(expr: &Expr, env: &Env) -> Expr {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            if let Some(atom) = env.get(s) {
                atom_to_expr(&atom).unwrap_or_else(|_| expr.clone())
            } else {
                expr.clone()
            }
        }
        Expr::List(items) => Expr::List(items.iter().map(|e| subst_expr_vars(e, env)).collect()),
        _ => expr.clone(),
    }
}
/// Evaluate `(|-> params body)` — lambda expression.
///
/// Creates a closure: captures the current lexical environment and stores
/// the parameter patterns and body expression. The closure is callable —
/// when applied, arguments are matched against params and body is evaluated
/// in the captured environment extended with the bindings.
fn eval_lambda(args: &[Expr], env: &Env) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "|->: expected (params body), got {} args", args.len()
        ));
    }
    let params = match &args[0] {
        Expr::List(items) => items.clone(),
        other => vec![other.clone()],
    };
    let closure = Atom::Closure(Box::new(crate::atom::ClosureData {
        params,
        body: args[1].clone(),
        env: env.clone(),
    }));
    Ok(NDet::single(closure))
}

/// Evaluate `(forall gen-expr check)` — universal quantification over NDet results.
///
/// Collects all results from `gen-expr`, applies `check` to each, returns
/// `true` if all pass (or generator is empty), `false` otherwise.
/// `check` can be a function name symbol or a closure.
fn eval_forall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!("forall: expected 2 args, got {}", args.len()));
    }
    // Use constrained eval for generator so free vars enumerate all clause solutions.
    let gen_values: Vec<Atom> = eval_constrained(&args[0], env, funcs)?
        .into_iter()
        .map(|(a, _)| a)
        .collect();
    let check = eval(&args[1], env, funcs)?
        .next()
        .ok_or_else(|| "forall: check produced no value".to_string())?;

    let arg_sym = Expr::Symbol("$__fv".to_string());
    for val in gen_values {
        let call_env = env.extend("$__fv", val);
        let results: Vec<Atom> = match &check {
            Atom::Sym(fname) => {
                let call = Expr::List(vec![Expr::Symbol(fname.to_string()), arg_sym.clone()]);
                eval(&call, &call_env, funcs)?.collect()
            }
            Atom::Closure(c) => {
                apply_closure(&c.params, &c.body, &c.env, &[arg_sym.clone()], &call_env, funcs)?
                    .collect()
            }
            other => return Err(format!(
                "forall: check must be a function or closure, got {}",
                other.to_sexpr_string()
            )),
        };
        if results.is_empty() || !results.iter().all(|a| a.is_truthy()) {
            return Ok(NDet::single(Atom::sym("false")));
        }
    }
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(call expr)` — evaluate the expression as a function call.
///
/// PeTTa semantics: translates to a direct predicate call at compile time.
/// In our runtime, this is equivalent to evaluating the single argument
/// as a normal expression (the dispatch loop handles function vs data).
///
/// `(reduce expr)` uses the same semantics — runtime dispatch evaluation.
fn eval_call(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("call: expected 1 arg, got {}", args.len()));
    }
    eval(&args[0], env, funcs)
}

/// Evaluate `(add-atom space atom)` — add an atom to the space.
///
/// This is a special form (not a builtin) because its arguments are NOT
/// evaluated before being passed — PeTTa semantics: `add-atom` receives
/// raw expressions so that `$` variable names in definitions are preserved
/// rather than triggering variable lookup errors.
fn eval_add_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "add-atom: expected (space atom), got {} args",
            args.len()
        ));
    }
    // Evaluate space reference (should evaluate to &self or similar)
    let mut space_results = eval(&args[0], env, funcs)?;
    let _space_ref = space_results.next().ok_or_else(|| {
        "add-atom: space expression produced no results".to_string()
    })?;
    // Convert the atom expression substituting bound $vars from env.
    // Bound vars (e.g. $body in evalCustom) get their values; unbound vars
    // (e.g. $N in (= (fib $N) ...)) stay as $-symbols. Matches PeTTa: add-atom
    // receives the Prolog term where unified variables already hold their values.
    let atom = subst_and_atomize(&args[1], env);
    funcs.space.borrow_mut().add_atom(&atom).map_err(|e| format!("add-atom: {}", e))?;
    // If the atom is a function definition (= head body), register the function
    if let Atom::Expr(items) = &atom {
        if items.len() == 3 && items[0] == Atom::sym("=") {
            if let (Ok(head_expr), Ok(body_expr)) = (
                atom_to_expr(&items[1]),
                atom_to_expr(&items[2]),
            ) {
                // compile_definition expects (= head body) — 3 elements.
                let def_expr = Expr::List(vec![
                    Expr::Symbol("=".to_string()),
                    head_expr,
                    body_expr,
                ]);
                if let Ok((name, clause)) = crate::compile::compile_definition(&def_expr) {
                    funcs.add_clause(name, clause.patterns, clause.body);
                }
            }
        }
    }
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(remove-atom space atom)` — remove an atom from the space.
/// Same special-form treatment as add-atom (arguments not pre-evaluated).
/// If the atom is a `(= head body)` definition, also removes the compiled clause
/// from the FnTable so space and cache stay in sync.
fn eval_remove_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "remove-atom: expected (space atom), got {} args",
            args.len()
        ));
    }
    // Evaluate space reference
    let mut space_results = eval(&args[0], env, funcs)?;
    let _space_ref = space_results.next().ok_or_else(|| {
        "remove-atom: space expression produced no results".to_string()
    })?;
    
    // In PeTTa, remove-atom uses pattern matching (like `retract/1`).
    // Substitute env-bound $vars first (e.g. $1/$2 bound by an enclosing match),
    // then match the atom as a pattern and remove all exact matches found.
    let expr = subst_expr_vars(&args[1], env);
    let pattern = crate::space::Pattern::from_expr(&expr);
    let matches = funcs.space.borrow().match_atoms(&pattern);
    let mut removed_any = false;
    
    for m in matches {
        if let Ok(removed) = funcs.space.borrow_mut().remove_atom(&m.atom) {
            if removed {
                removed_any = true;
                // Keep FnTable in sync: if removed atom was a function definition, drop its clause.
                if let Atom::Expr(items) = &m.atom {
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
                                funcs.remove_clause(&name, &clause.patterns, &clause.body);
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(NDet::single(if removed_any {
        Atom::sym("true")
    } else {
        Atom::sym("")
    }))
}

/// Evaluate `(match space pattern body)` — pattern match atoms in a space.
///
/// Evaluates `space` to get the space reference, converts `pattern` to a
/// `Pattern`, queries the space for matching atoms, then evaluates `body`
/// once per match with variables bound from the pattern.
///
/// PeTTa semantics: `match(Space, Pattern, Out, Out)` — matches atoms in
/// the space, binds variables from the pattern to the matched atom.
fn eval_match(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "match: expected (space pattern body), got {} args",
            args.len()
        ));
    }
    // Evaluate space reference (must evaluate to &self or similar)
    let mut space_results = eval(&args[0], env, funcs)?;
    let _space_ref = space_results.next().ok_or_else(|| {
        "match: space expression produced no results".to_string()
    })?;
    // Build pattern: substitute any already-bound variables in the pattern expression
    // (e.g., in nested matches, $2 might be bound from outer match), then build pattern.
    let pattern = if let Expr::Symbol(s) = &args[1] {
        if s.starts_with('$') {
            if let Some(atom) = env.get(s) {
                Pattern::from_atom(&atom)
            } else {
                Pattern::from_expr(&args[1])
            }
        } else {
            Pattern::from_expr(&args[1])
        }
    } else {
        let substituted = subst_expr_vars(&args[1], env);
        Pattern::from_expr(&substituted)
    };
    // Query the space
    let matches = {
        let space = funcs.space.borrow();
        space.match_atoms(&pattern)
    };
    if matches.is_empty() {
        return Ok(NDet::Single(None)); // empty stream — no match
    }
    // Template: if args[2] is a $var bound in env, resolve to atom then convert to
    // expr so that match bindings (e.g. $1 → 1) are applied when evaluating it.
    let template: Expr = if let Expr::Symbol(s) = &args[2] {
        if s.starts_with('$') {
            if let Some(atom) = env.get(s) {
                atom_to_expr(&atom)?
            } else {
                args[2].clone()
            }
        } else {
            args[2].clone()
        }
    } else {
        args[2].clone()
    };
    // Evaluate template for each match with variable bindings
    let streams: Result<Vec<NDet>, String> = matches
        .into_iter()
        .map(|result| {
            let mut match_env = env.clone();
            for (name, val) in &result.bindings {
                match_env = match_env.extend(name, val.clone());
            }
            eval(&template, &match_env, funcs)
        })
        .collect();
    Ok(NDet::stream(streams?.into_iter().flatten()))
}

/// Evaluate `(import! space path)` — load a MeTTa file into the space.
///
/// Path resolution order (first match wins, each tried with and without `.metta`):
///   1. As-is from CWD
///   2. Relative to the importing file's directory (`funcs.import_dir`)
///
/// Files are loaded with a streaming form-by-form parser — only one balanced
/// expression is held in memory at a time, so billion-line data files are safe.
/// `import_dir` is updated for the duration of the nested load so that imports
/// inside an imported file also resolve relative to their own location.
fn eval_import(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "import!: expected (space path), got {} args",
            args.len()
        ));
    }
    // Evaluate space reference
    let mut space_results = eval(&args[0], env, funcs)?;
    let _space_ref = space_results.next().ok_or_else(|| {
        "import!: space expression produced no results".to_string()
    })?;
    // Extract path string
    let path_str = match &args[1] {
        Expr::Symbol(s) => s.clone(),
        Expr::Number(_) => return Err("import!: file path must be a symbol, not a number".into()),
        Expr::List(_)   => return Err("import!: file path must be a symbol, not a list".into()),
    };
    // Resolve path: CWD first, then relative to the importing file's directory.
    let import_dir = funcs.import_dir.borrow().clone();
    let resolved = resolve_import_path(&path_str, &import_dir)
        .ok_or_else(|| format!(
            "import!: cannot find '{}' (searched CWD and '{}')",
            path_str, import_dir.display()
        ))?;
    // Push the imported file's directory so nested imports resolve relative to it.
    let new_dir = resolved.parent()
        .unwrap_or(std::path::Path::new("."))
        .to_path_buf();
    let prev_dir = funcs.import_dir.replace(new_dir);
    let result = load_metta_file(&resolved, env, funcs);
    funcs.import_dir.replace(prev_dir);
    result?;
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(import-rs! name)` — compile and load a Rust plugin.
///
/// `name` can be a bare library name (e.g. `my_math`) or a path to a `.rs` file.
/// Search order: same dir as the importing file, then CWD, then bare path.
///
/// Requires building with `--features plugins`.
#[cfg(feature = "plugins")]
fn eval_import_rs(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("import-rs!: expected 1 arg (library name), got {}", args.len()));
    }
    let name = match &args[0] {
        Expr::Symbol(s) => s.as_str(),
        _ => return Err("import-rs!: argument must be a symbol (library name)".into()),
    };
    if name.is_empty() {
        return Err("import-rs!: library name cannot be empty".into());
    }

    // Build search directories: importing file's dir, libs/, then CWD
    let import_dir = funcs.import_dir.borrow().clone();
    let mut search_dirs: Vec<PathBuf> = Vec::new();
    if !import_dir.as_os_str().is_empty() {
        search_dirs.push(import_dir.clone());
        search_dirs.push(import_dir.join("libs"));
    }
    search_dirs.push(PathBuf::from("."));
    search_dirs.push(PathBuf::from("./libs"));

    let lib_name = crate::plugin::import_rs(name, funcs, &search_dirs)
        .map_err(|e| format!("import-rs!: {}", e))?;

    // Also load a companion .metta file if it exists
    let metta_name = format!("{}.metta", lib_name);
    for dir in &search_dirs {
        let metta_path = dir.join(&metta_name);
        if metta_path.exists() {
            let _ = load_metta_file(&metta_path, env, funcs)?;
            break;
        }
    }

    trace!("import-rs!: loaded plugin '{}'", lib_name);
    Ok(NDet::single(Atom::sym(&lib_name)))
}

/// Stub when `plugins` feature is disabled.
#[cfg(not(feature = "plugins"))]
fn eval_import_rs(args: &[Expr], _env: &Env, _funcs: &FnTable) -> Result<NDet, String> {
    let _ = args; // suppress unused
    Err("import-rs!: this interpreter was built without the 'plugins' feature (rebuild with --features plugins)".into())
}

/// Resolve an import path against a priority-ordered list of base directories.
///
/// Search order (first hit wins, each tried with and without `.metta`):
///   1. CWD — for absolute or CWD-relative paths
///   2. `import_dir` — relative to the importing file's own directory
///   3. Parent of CWD — for paths written relative to the project root when
///      the binary is run from a subdirectory (e.g. `metta/examples/lib_he`
///      resolves from `MORK/` when `cargo run` is invoked from `MORK/metta/`)
fn resolve_import_path(
    path_str: &str,
    import_dir: &std::path::Path,
) -> Option<std::path::PathBuf> {
    let parent_cwd = std::env::current_dir()
        .ok()
        .and_then(|d| d.parent().map(|p| p.to_path_buf()));

    let bases = std::iter::once(std::path::PathBuf::from("."))
        .chain(std::iter::once(import_dir.to_path_buf()))
        .chain(parent_cwd);

    for base in bases {
        for candidate in [base.join(path_str), base.join(format!("{}.metta", path_str))] {
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    None
}

/// Stream-load a `.metta` file: parse one balanced form at a time and process
/// it immediately, so only O(1-form) memory is used regardless of file size.
///
/// Returns the first result of the last runnable form, or `None` if the file
/// ends with a definition (matching the semantics of `load_form`).
pub fn load_metta_file(
    path: &std::path::Path,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<Atom>, String> {
    use std::io::{BufRead, BufReader};
    let file = std::fs::File::open(path)
        .map_err(|e| format!("cannot open '{}': {}", path.display(), e))?;
    let mut form_buf = String::with_capacity(256);
    let mut depth: i32 = 0;
    let mut saw_bang = false;
    let mut results: Vec<Atom> = Vec::new();
    for (line_no, line_result) in BufReader::new(file).lines().enumerate() {
        let line = line_result
            .map_err(|e| format!("read error at line {} in '{}': {}", line_no + 1, path.display(), e))?;
        for ch in line.chars() {
            match ch {
                ';' => break,           // rest of line is a comment
                '!' if depth == 0 => saw_bang = true,
                '(' => { depth += 1; form_buf.push(ch); }
                ')' if depth > 0 => {
                    depth -= 1;
                    form_buf.push(ch);
                    if depth == 0 {
                        if let Some(result) = process_form(&form_buf, saw_bang, env, funcs)
                            .map_err(|e| format!("{} (in '{}' near line {})", e, path.display(), line_no + 1))?
                        {
                            results.push(result);
                        }
                        form_buf.clear();
                        saw_bang = false;
                    }
                }
                ')' => return Err(format!("unmatched ')' in '{}' at line {}", path.display(), line_no + 1)),
                _ if depth > 0 => form_buf.push(ch),
                _ => {}                 // whitespace / other between forms
            }
        }
    }
    if depth != 0 {
        return Err(format!("unclosed '(' in '{}'", path.display()));
    }
    Ok(results)
}

/// Parse a single buffered form string and dispatch it.
fn process_form(
    form: &str,
    is_runnable: bool,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Atom>, String> {
    let prefixed;
    let src: &str = if is_runnable {
        prefixed = format!("!{}", form);
        &prefixed
    } else {
        form
    };
    let mut last = None;
    for top_form in crate::parser::parse_forms(src)? {
        last = process_top_form(top_form, env, funcs)?;
    }
    Ok(last)
}

/// Process a single top-level form: store+compile definitions, eval runnables.
fn process_top_form(form: TopForm, env: &Env, funcs: &FnTable) -> Result<Option<Atom>, String> {
    match form {
        TopForm::Definition(expr) => {
            let atom = expr_to_atom(&expr);
            funcs.space.borrow_mut().add_atom(&atom)
                .map_err(|e| format!("add_atom: {}", e))?;
            if let Ok((name, clause)) = crate::compile::compile_definition(&expr) {
                funcs.add_clause(name, clause.patterns, clause.body);
            }
            Ok(None)
        }
        TopForm::Runnable(expr) => {
            let mut results = eval(&expr, env, funcs)?;
            Ok(results.next())
        }
    }
}

/// Evaluate `(readln!)` — read a line from stdin and parse it.
fn eval_readln(_args: &[Expr], _env: &Env, _funcs: &FnTable) -> Result<NDet, String> {
    use std::io::{self, Write};
    let mut input = String::new();
    io::stdout().flush().map_err(|e| e.to_string())?;
    io::stdin().read_line(&mut input).map_err(|e| e.to_string())?;
    let wrapped = format!("({})", input);
    match crate::parser::parse_forms(&wrapped) {
        Ok(forms) => {
            if let Some(crate::parser::TopForm::Definition(crate::parser::Expr::List(mut items))) = forms.into_iter().next() {
                if items.len() == 1 {
                    Ok(NDet::single(crate::parser::expr_to_atom(&items.remove(0))))
                } else if items.is_empty() {
                    Ok(NDet::single(crate::atom::Atom::Expr(vec![])))
                } else {
                    Ok(NDet::single(crate::atom::Atom::Expr(
                        items.into_iter().map(|e| crate::parser::expr_to_atom(&e)).collect()
                    )))
                }
            } else {
                Err("readln!: Could not parse input".to_string())
            }
        }
        Err(e) => Err(format!("readln!: Parse error: {}", e)),
    }
}

/// Evaluate `(println! args...)` — print values to stdout (for debugging).
/// Each arg is evaluated and its results printed space-separated.
/// If a single arg is a non-empty list, its elements are printed space-separated.
fn eval_println(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let mut parts = Vec::new();
    for arg in args {
        let mut results = eval(arg, env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("println!: argument produced no results: {:?}", arg)
        })?;
        if let Atom::Expr(items) = &val {
            let s: Vec<String> = items.iter().map(|a| a.to_sexpr_string()).collect();
            parts.push(s.join(" "));
        } else {
            parts.push(val.to_sexpr_string());
        }
    }
    println!("{}", parts.join(" "));
    // PeTTa: 'println!'(Arg, true) — return value is always true.
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(eval expr)` — re-evaluate a raw expression as code.
///
/// PeTTa: the translator emits `eval(RawArg, Out)` where RawArg is the
/// *untranslated* source term. `eval/2` then re-translates and runs it.
/// This means `(eval (quote (fib 5)))` returns `(fib 5)` as data (quote
/// stops the inner eval), not 5.
///
/// For a `$var`, the variable's atom value is treated as code and evaluated.
/// For any other literal expression, it is passed directly to eval.
fn eval_eval(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("eval: expected 1 arg, got {}", args.len()));
    }
    match &args[0] {
        Expr::Symbol(s) if s.starts_with('$') => {
            // $var: retrieve the atom it holds, convert to code, evaluate.
            let val = env
                .get(s)
                .ok_or_else(|| format!("eval: unbound variable {}", s))?;
            let expr = atom_to_expr(&val)?;
            eval(&expr, env, funcs)
        }
        // Literal expression: pass directly to eval — no pre-evaluation.
        _ => eval(&args[0], env, funcs),
    }
}

/// Evaluate `(superpose expr)` — spread elements of a list or atom into a stream.
///
/// PeTTa semantics: `superpose(L,X) :- member(X,L)`. Takes a single argument.
/// If the argument is a literal list `(a b c)`, evaluate each element and include
/// its full result stream. If the argument evaluates to an `Atom::Expr`, unpack
/// its elements. Otherwise return the atom as a single result.
fn eval_superpose(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err("superpose: expected exactly 1 argument (a list)".into());
    }
    let arg = &args[0];
    // Literal list: evaluate each element, produce their full streams
    if let Expr::List(items) = arg {
        let streams: Result<Vec<NDet>, String> = items
            .iter()
            .map(|e| eval(e, env, funcs))
            .collect();
        return Ok(NDet::stream(streams?.into_iter().flatten()));
    }
    // Non-list: evaluate, then unpack if Expr value
    let mut results = eval(arg, env, funcs)?;
    let val = results.next().ok_or_else(|| {
        "superpose: argument produced no results".to_string()
    })?;
    match val {
        Atom::Expr(elements) => Ok(NDet::stream(elements.into_iter())),
        other => Ok(NDet::single(other)),
    }
}

/// Evaluate `(collapse expr)` — collect all results into a list atom.
fn eval_collapse(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("collapse: expected 1 arg, got {}", args.len()));
    }
    let results: Vec<Atom> = eval(&args[0], env, funcs)?.collect();
    Ok(NDet::single(Atom::Expr(results)))
}

/// Evaluate `(foldall agg-func gen-expr init)` — fold over a nondeterministic stream.
///
/// Collects all results from `gen-expr`, then folds them using `agg-func`:
/// `agg(agg(agg(init, v1), v2), v3) ...`. Returns the final accumulator.
///
/// When `gen-expr` contains unbound `$`-variables (e.g. `(g $x)` where `$x` is
/// free), the function attempts free-variable resolution: it finds each clause
/// of the generator's function and extracts literal values from the clause
/// patterns at the free-variable position, then calls the function with each
/// concrete value.
///
/// PeTTa reference: `foldall` aggregates over all solutions of a generator.
fn eval_foldall(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "foldall: expected (agg-func gen-expr init), got {} args",
            args.len()
        ));
    }
    let agg_func = &args[0];
    // Collect all values from generator — try normal eval first, then
    // fall back to free-variable resolution if the expression has unbound vars.
    let gen_values: Vec<Atom> = match eval(&args[1], env, funcs) {
        Ok(results) => results.collect(),
        Err(_) => generate_free_var_values(&args[1], env, funcs)?,
    };
    // Evaluate init value (first result)
    let mut init_results = eval(&args[2], env, funcs)?;
    let init = init_results.next().ok_or_else(|| {
        "foldall: init expression produced no results".to_string()
    })?;
    // Fold: accum = agg(accum, next) for each gen value
    let accum = gen_values.into_iter().try_fold(init, |acc, val| {
        let acc_expr = atom_to_expr(&acc)?;
        let val_expr = atom_to_expr(&val)?;
        let call = Expr::List(vec![agg_func.clone(), acc_expr, val_expr]);
        let mut results = eval(&call, env, funcs)?;
        results.next().ok_or_else(|| {
            "foldall: aggregate function produced no results".to_string()
        })
    })?;
    Ok(NDet::single(accum))
}
/// Try to generate values from a function call expression with free variables.
///
/// When a generator like `(g $x)` contains an unbound `$x`, this function
/// looks up `g` in the function table, iterates over its clauses, and for
/// each clause extracts the literal value at the free-variable position.
/// It then calls `g` with each literal value and collects the results.
///
/// Currently only handles the single-free-variable case with literal (number
/// or symbol) patterns. Nested patterns or multiple free variables are not
/// supported and return an error.
fn generate_free_var_values(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    let items = match expr {
        Expr::List(items) if !items.is_empty() => items,
        _ => return Err(format!(
            "generator: expected a function call, got {}", expr.to_string()
        )),
    };
    let op = &items[0];
    let arity = items.len() - 1;
    // Evaluate the operator to get the function name
    let op_atom = match eval(op, env, funcs)?.next() {
        Some(a) => a,
        None => return Err("generator: operator produced no results".into()),
    };
    // Closure generator: (closure arg...) — bind params to concrete args (if any),
    // then eval or recurse on the body with the remaining free variables.
    if let Atom::Closure(c) = &op_atom {
        let (params, body, capture_env) = (&c.params, &c.body, &c.env);
        let mut closure_env = capture_env.clone();
        for (param, arg_expr) in params.iter().zip(items[1..].iter()) {
            let is_free = matches!(arg_expr, Expr::Symbol(s) if s.starts_with('$') && env.get(s).is_none());
            if !is_free {
                if let Ok(mut evaled) = eval(arg_expr, env, funcs) {
                    if let Some(val) = evaled.next() {
                        if let Expr::Symbol(pname) = param {
                            closure_env = closure_env.extend(pname, val);
                        }
                    }
                }
            }
        }
        let body_results: Vec<Atom> = match eval(body, &closure_env, funcs) {
            Ok(r) => r.collect(),
            Err(_) => generate_free_var_values(body, &closure_env, funcs)?,
        };
        return Ok(body_results);
    }
    let fname = match &op_atom {
        Atom::Sym(s) => s.clone(),
        _ => return Err(format!(
            "generator: expected function name, got {}", op_atom.to_sexpr_string()
        )),
    };
    // SAFETY: arity = items.len() - 1; items is non-empty (guarded above), so arity < 256.
    let func_ref = funcs.get_ref(&fname, arity as u8).ok_or_else(|| {
        format!("generator: unknown function {} with {} args", fname, arity)
    })?;
    let (clauses, native_func): (Vec<Clause>, Option<Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + 'static>>) = match &func_ref.kind {
        FunctionKind::UserDefined { clauses } => (clauses.clone(), None),
        FunctionKind::Native { func: f } => (vec![], Some(Arc::clone(f))),
    };
    let is_native = matches!(&func_ref.kind, FunctionKind::Native { .. });
    drop(func_ref); // Release RefCell borrow before recursive eval calls.
    if is_native {
        if let Some(f) = native_func {
            // For each arg, collect all possible values:
            // concrete args → one value; free-var args → recurse to get many values.
            // Then call the native with every combination (cartesian product).
            let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(arity);
            for arg_expr in &items[1..] {
                match eval(arg_expr, env, funcs) {
                    Ok(nd) => {
                        let vals: Vec<Atom> = nd.collect();
                        if vals.is_empty() { return Ok(vec![]); }
                        arg_options.push(vals);
                    }
                    Err(_) => {
                        // eval failed — treat as free variable generation
                        let opts = generate_free_var_values(arg_expr, env, funcs)?;
                        arg_options.push(opts);
                    }
                }
            }
            // Cartesian product
            let mut results = Vec::new();
            let mut indices = vec![0usize; arg_options.len()];
            loop {
                let args_slice: Vec<Atom> = indices.iter().enumerate()
                    .map(|(i, &idx)| arg_options[i][idx].clone())
                    .collect();
                if let Ok(mut nd) = f(&args_slice, funcs) {
                    while let Some(a) = nd.next() {
                        results.push(a);
                    }
                }
                // Increment indices
                let mut i = indices.len();
                while i > 0 {
                    i -= 1;
                    indices[i] += 1;
                    if indices[i] < arg_options[i].len() {
                        break;
                    }
                    indices[i] = 0;
                    if i == 0 { return Ok(results); }
                }
            }
        }
        return Err("generator: unexpected native dispatch failure".into());
    }
    // UserDefined
    let mut results = Vec::new();
    for clause in &clauses {
        if clause.patterns.len() != arity {
            continue;
        }
        let mut concrete_args = Vec::with_capacity(arity);
        let mut has_free = false;
        for (i, arg_expr) in items[1..].iter().enumerate() {
            if let Expr::Symbol(s) = arg_expr {
                if s.starts_with('$') && env.get(s).is_none() {
                    match &clause.patterns[i] {
                        Expr::Number(n) => {
                            concrete_args.push(Atom::Num(*n));
                            has_free = true;
                        }
                        Expr::Symbol(sym) if !sym.starts_with('$') => {
                            concrete_args.push(Atom::sym(&sym));
                            has_free = true;
                        }
                        _ => {
                            concrete_args.clear();
                            break;
                        }
                    }
                    continue;
                }
            }
            // Normal evaluation
            let mut evaled = eval(arg_expr, env, funcs)?;
            match evaled.next() {
                Some(a) => concrete_args.push(a),
                None => { concrete_args.clear(); break; }
            }
        }
        if !has_free || concrete_args.len() != arity {
            continue;
        }
        let mut matched = true;
        let mut match_env = Env::new();
        for (pat, arg_val) in clause.patterns.iter().zip(concrete_args.iter()) {
            match try_match_one(pat, arg_val, &match_env, funcs)? {
                Some(new_env) => match_env = new_env,
                None => { matched = false; break; }
            }
        }
        if !matched {
            continue;
        }
        let new_env = prepend_env(match_env, env);
        let mut body_results = eval(&clause.body, &new_env, funcs)?;
        while let Some(atom) = body_results.next() {
            results.push(atom);
        }
    }
    if results.is_empty() {
        return Err(format!(
            "generator: {}: no clauses with literal patterns for free variables",
            fname
        ));
    }
    Ok(results)
}

/// Evaluate `(map-atom list func)` — apply `func` to each element of `list`.
///
/// PeTTa runtime: `'map-atom'([H|T], Func, [R|RT]) :- reduce([Func,H], R)`.
/// `reduce/2` dispatches on Func type:
///   - registered atom → direct call
///   - closure         → apply_closure
///   - anything else   → produce `[Func, H]` as data (no error)
fn eval_map_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "map-atom: expected (list func), got {} args",
            args.len()
        ));
    }
    let mut list_results = eval(&args[0], env, funcs)?;
    let list_atom = list_results.next().ok_or_else(|| {
        "map-atom: list expression produced no results".to_string()
    })?;
    let mut func_results = eval(&args[1], env, funcs)?;
    let func_atom = func_results.next().ok_or_else(|| {
        "map-atom: func expression produced no results".to_string()
    })?;
    // Move elements out — list_atom not needed after this.
    let elements = match list_atom {
        Atom::Expr(items) => items,
        other => return Err(format!(
            "map-atom: expected a list (Expr), got {}",
            other.to_sexpr_string()
        )),
    };
    let mut results = Vec::with_capacity(elements.len());
    for elem in &elements {
        // reduce([Func, H], R) dispatch:
        let result = match &func_atom {
            Atom::Sym(fname) => {
                let elem_expr = atom_to_expr(elem)?;
                let call_expr = Expr::List(vec![Expr::Symbol(fname.to_string()), elem_expr]);
                let mut r = eval(&call_expr, env, funcs)?;
                r.next().ok_or_else(|| format!(
                    "map-atom: {} returned no result for {}",
                    fname, elem.to_sexpr_string()
                ))?
            }
            Atom::Closure(c) => {
                let elem_expr = atom_to_expr(elem)?;
                let mut r = apply_closure(&c.params, &c.body, &c.env, &[elem_expr], env, funcs)?;
                r.next().ok_or_else(|| format!(
                    "map-atom: closure returned no result for {}",
                    elem.to_sexpr_string()
                ))?
            }
            // reduce case 3: unknown func → [Func, H] as data
            _ => Atom::Expr(vec![func_atom.clone(), elem.clone()]),
        };
        results.push(result);
    }
    Ok(NDet::single(Atom::Expr(results)))
}

/// Evaluate `(chain expr $var expr $var ... final-expr)` — thread value through
/// a pipeline of expressions.
///
/// Each expression is evaluated in order; its first result is bound to the
/// following `$var`, making it available to subsequent expressions. The final
/// expression's result is the overall result.
///
/// PeTTa reference: `chain(Value, Var, Expr, ...)` compiles to
/// `substitute(Value, Var, Expr, ChainResult)`.
///
/// # Errors
/// Returns error if any `$var` position is not a `$`-prefixed symbol, if any
/// expression produces no results, or if arg count is even.
fn eval_chain(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() == 1 {
        // Single expression: evaluate and return directly
        return eval(&args[0], env, funcs);
    }
    if args.len() < 3 || args.len() % 2 == 0 {
        return Err(format!(
            "chain: expected odd number of args (expr $var expr ...), got {}",
            args.len()
        ));
    }
    let mut current_env = env.clone();
    let last_idx = args.len() - 1;

    // Process (expr, $var) pairs up to the last expression
    let pairs = args.len() / 2; // integer division
    for i in 0..pairs {
        let expr = &args[i * 2];
        let var = &args[i * 2 + 1];

        // Var must be a $variable
        let var_name = match var {
            Expr::Symbol(s) if s.starts_with('$') => s.clone(),
            _ => return Err(format!(
                "chain: arg {} must be a $variable, got {}",
                i * 2 + 1, var.to_string()
            )),
        };

        // Evaluate expression, take first result
        let mut results = eval(expr, &current_env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("chain: expression {} produced no results", i * 2)
        })?;

        current_env = current_env.extend(&var_name, val);
    }

    // Evaluate final expression
    eval(&args[last_idx], &current_env, funcs)
}

/// Evaluate `(case expr (pattern1 body1) (pattern2 body2) ...)` — pattern match dispatch.
///
/// Evaluates `expr`, takes the first result, then tries each clause's pattern
/// against it (in order). The first matching clause's body is evaluated with
/// the matched bindings. `$else` always matches as a catch-all.
///
/// PeTTa reference: `case(Value, PatternBodyPairs)` compiles to
/// match-then-evaluate over the list of (pattern, body) pairs.
///
/// # Errors
/// Returns error if no clause matches the value.
fn eval_case(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "case: expected (expr (clauses...)), got {} args",
            args.len()
        ));
    }

    // Get clauses list up front
    let clauses = match &args[1] {
        Expr::List(items) => items,
        _ => return Err("case: second arg must be a list of (pattern body) pairs".into()),
    };

    // Collect all scrutinee values (may be nondeterministic)
    let vals: Vec<Atom> = eval(&args[0], env, funcs)?.collect();

    // Empty scrutinee: look for (Empty body) clause
    if vals.is_empty() {
        for clause in clauses {
            let (pattern, body) = match clause {
                Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
                _ => continue,
            };
            if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
                return eval(body, env, funcs);
            }
        }
        return Ok(NDet::stream(std::iter::empty()));
    }

    // Fan out: for each scrutinee value, match clauses and collect results
    let mut out: Vec<Atom> = Vec::new();
    for val in vals {
        let mut matched = false;
        for clause in clauses {
            let (pattern, body) = match clause {
                Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
                _ => return Err(format!(
                    "case: each clause must be (pattern body), got {}",
                    clause.to_string()
                )),
            };

            if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
                continue;
            }

            if matches!(pattern, Expr::Symbol(s) if s == "$else") {
                out.extend(eval(body, env, funcs)?);
                matched = true;
                break;
            }

            if let Some(match_env) = try_match_one(pattern, &val, &Env::new(), funcs)? {
                let new_env = prepend_env(match_env, env);
                out.extend(eval(body, &new_env, funcs)?);
                matched = true;
                break;
            }
        }
        if !matched {
            return Err(format!(
                "case: no clause matched value {}", val.to_sexpr_string()
            ));
        }
    }
    Ok(NDet::stream(out.into_iter()))
}

// -----------------------------------------------------------------------
// py-call — Python bridge via PyO3 (feature: python-bridge)
// -----------------------------------------------------------------------

/// Evaluate `(py-call module func arg1 arg2 ...)`.
///
/// Calls a Python function from a module with the given arguments.
/// - `module` — Python module name (string)
/// - `func` — function name within the module (string)
/// - `arg1 arg2 ...` — arguments converted to Python objects
///
/// Returns the Python result converted back to a MeTTa atom.
/// Requires building with `--features python-bridge`.
fn eval_py_call(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() < 2 {
        return Err(format!(
            "py-call: expected at least (module func), got {} args",
            args.len()
        ));
    }
    #[cfg(feature = "python-bridge")]
    {
        return eval_py_call_impl(args, env, funcs);
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        let _ = env;
        let _ = funcs;
        Err("py-call: python-bridge feature not enabled. Rebuild with --features python-bridge".into())
    }
}

#[cfg(feature = "python-bridge")]
fn eval_py_call_impl(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    use pyo3::prelude::*;

    /// Convert a MeTTa atom to a Python object.
    fn atom_to_py<'py>(atom: &Atom, py: Python<'py>) -> Result<Bound<'py, PyAny>, String> {
        match atom {
            Atom::Num(n) => {
                // Convert i128 to Python int via PyO3's IntoPyObject
                let obj = n.into_pyobject(py)
                    .map_err(|e| format!("py-call: failed to convert number {}: {}", n, e))?;
                Ok(obj.into_any())
            }
            Atom::Sym(s) => {
                let py_str = pyo3::types::PyString::new(py, &**s);
                Ok(py_str.into_any())
            }
            Atom::Expr(items) => {
                let list = pyo3::types::PyList::empty(py);
                for item in items {
                    let obj = atom_to_py(item, py)?;
                    list.append(obj)
                        .map_err(|e| format!("py-call: failed to build list: {}", e))?;
                }
                Ok(list.into_any())
            }
            Atom::Closure(_) => {
                let s = atom.to_sexpr_string();
                let py_str = pyo3::types::PyString::new(py, &s);
                Ok(py_str.into_any())
            }
        }
    }

    /// Convert a Python object back to a MeTTa atom.
    fn py_to_atom(obj: &Bound<'_, PyAny>) -> Result<Atom, String> {
        // Try int first
        if let Ok(n) = obj.extract::<i128>() {
            return Ok(Atom::Num(n));
        }
        // Try float
        if let Ok(f) = obj.extract::<f64>() {
            // Store as a numeric symbol string to match PeTTa float convention
            let s = format!("{}", f);
            return Ok(Atom::sym(&s));
        }
        // Try string
        if let Ok(s) = obj.extract::<String>() {
            return Ok(Atom::sym(&s));
        }
        // Try bool
        if let Ok(b) = obj.extract::<bool>() {
            return Ok(if b { Atom::sym("True") } else { Atom::sym("False") });
        }
        // Try None
        if obj.is_none() {
            return Err("py-call: Python function returned None".into());
        }
        // Try list/tuple — manually iterate since PyList doesn't extract to Vec<Bound>
        if let Ok(list) = obj.downcast::<pyo3::types::PyList>() {
            let atoms: Result<Vec<Atom>, String> = list.iter().map(|item| py_to_atom(&item)).collect();
            return Ok(Atom::Expr(atoms?));
        }
        if let Ok(tup) = obj.downcast::<pyo3::types::PyTuple>() {
            let atoms: Result<Vec<Atom>, String> = tup.iter().map(|item| py_to_atom(&item)).collect();
            return Ok(Atom::Expr(atoms?));
        }
        // Fallback: use repr string
        let repr_val = obj.repr()
            .map(|r| r.to_string_lossy().to_string())
            .unwrap_or_else(|_| "<unprintable>".to_string());
        Ok(Atom::sym(&repr_val))
    }

    // Evaluate module name arg
    let mut mod_results = eval(&args[0], env, funcs)?;
    let mod_atom = mod_results.next().ok_or_else(|| {
        "py-call: module expression produced no results".to_string()
    })?;
    let mod_name = match &mod_atom {
        Atom::Sym(s) => s.trim_matches('"').to_string(),
        other => return Err(format!(
            "py-call: module must be a symbol, got {}", other.to_sexpr_string()
        )),
    };

    // Evaluate function name arg
    let mut func_results = eval(&args[1], env, funcs)?;
    let func_atom = func_results.next().ok_or_else(|| {
        "py-call: function expression produced no results".to_string()
    })?;
    let func_name = match &func_atom {
        Atom::Sym(s) => s.trim_matches('"').to_string(),
        other => return Err(format!(
            "py-call: function must be a symbol, got {}", other.to_sexpr_string()
        )),
    };

    // Evaluate remaining args
    let mut py_args: Vec<Atom> = Vec::with_capacity(args.len().saturating_sub(2));
    for arg in &args[2..] {
        let mut arg_results = eval(arg, env, funcs)?;
        let arg_atom = arg_results.next().ok_or_else(|| {
            format!("py-call: argument expression produced no results")
        })?;
        py_args.push(arg_atom);
    }

    // Execute Python call (lazy init — auto-initialize handles it)
    Python::with_gil(|py| {
        // Import module
        let module = py.import(AsRef::<str>::as_ref(&mod_name))
            .map_err(|e| format!("py-call: cannot import module '{}': {}", mod_name, e))?;

        // Get function
        let func = module.getattr(AsRef::<str>::as_ref(&func_name))
            .map_err(|e| format!("py-call: module '{}' has no function '{}': {}", mod_name, func_name, e))?;

        // Convert args to Python objects
        let py_objs: Result<Vec<Bound<'_, PyAny>>, String> = py_args.iter()
            .map(|a| atom_to_py(a, py))
            .collect();
        let py_objs = py_objs?;

        // Call function — build a tuple from the args
        let args_tuple = pyo3::types::PyTuple::new(py, &py_objs)
            .map_err(|e| format!("py-call: failed to build args tuple: {}", e))?;
        let result = func.call(&args_tuple, None)
            .map_err(|e| format!("py-call: error calling {}.{}: {}", mod_name, func_name, e))?;

        // Convert result back
        let atom = py_to_atom(&result)?;
        Ok(NDet::single(atom))
    })
}
