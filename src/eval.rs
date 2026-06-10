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
use crate::func::{FnTable, Function, FunctionKind, NDet};
use crate::parser::{atom_to_expr, expr_to_atom, parse_forms, Expr, TopForm};
use crate::space::Pattern;
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
                let val = env
                    .get(s)
                    .ok_or_else(|| format!("unbound variable: {}", s))?;
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
                    "println!" => { trace!("→ special: println!"); return eval_println(args, env, funcs); }
                    "superpose" => { trace!("→ special: superpose"); return eval_superpose(args, env, funcs); }
                    "collapse" => { trace!("→ special: collapse"); return eval_collapse(args, env, funcs); }
                    "chain" => { trace!("→ special: chain"); return eval_chain(args, env, funcs); }
                    "case" => { trace!("→ special: case"); return eval_case(args, env, funcs); }
                    "foldall" => { trace!("→ special: foldall"); return eval_foldall(args, env, funcs); }
                    "map-atom" => { trace!("→ special: map-atom"); return eval_map_atom(args, env, funcs); }
                    "|->" => { trace!("→ special: lambda"); return eval_lambda(args, env); }
                    // empty produces no results (Prolog fail / empty nondeterminism)
                    "empty" => { trace!("→ special: empty"); return Ok(NDet::stream(std::iter::empty())); }
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
        None => return eval_data_list(all_items, env, funcs),
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
    // Fallback: data list — collect evaluated elements into one Expr atom.
    trace!("→ fallback: data list");
    eval_data_list(all_items, env, funcs)
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
    trace_enter!("call: {} ({} args)", op_name, args.len());
    // Evaluate arguments (take first result of each)
    let mut arg_vals = Vec::with_capacity(args.len());
    for (i, arg) in args.iter().enumerate() {
        let mut results = eval(arg, env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("{}: argument {} produced no results", op_name, i + 1)
        })?;
        arg_vals.push(val);
    }
    // arg_strs only needed for trace output — gate behind the feature flag so
    // normal builds pay zero cost (no string allocations on 2.7M fib calls).
    #[cfg(feature = "trace")]
    let arg_strs: Vec<String> = arg_vals.iter().map(|a| a.to_sexpr_string()).collect();
    trace!("{} args: [{}]", op_name, arg_strs.join(", "));
    let result = match &func.kind {
        FunctionKind::Native { func: f } => f(&arg_vals, funcs),
        FunctionKind::UserDefined { clauses } => {
            // Fast path: single clause avoids Vec<NDet> + Box allocation
            if clauses.len() == 1 {
                return match try_match_clause(&clauses[0].patterns, &arg_vals, env, funcs)? {
                    Some(new_env) => {
                        trace!("clause matched, body eval");
                        eval(&clauses[0].body, &new_env, funcs)
                    }
                    None => Err(format!(
                        "{}: no matching clause for args [{}]",
                        op_name,
                        arg_vals.iter().map(|a| a.to_sexpr_string()).collect::<Vec<_>>().join(", ")
                    )),
                };
            }
            // Multi-clause: collect all matching results into a nondeterministic stream
            let mut streams: Vec<NDet> = Vec::new();
            for clause in clauses.iter() {
                match try_match_clause(&clause.patterns, &arg_vals, env, funcs)? {
                    Some(new_env) => {
                        trace!("clause matched, body eval");
                        streams.push(eval(&clause.body, &new_env, funcs)?);
                    }
                    None => {
                        trace!("clause did not match, trying next");
                    }
                }
            }
            if streams.is_empty() {
                return Err(format!(
                    "{}: no matching clause for args [{}]",
                    op_name,
                    arg_vals.iter().map(|a| a.to_sexpr_string()).collect::<Vec<_>>().join(", ")
                ));
            }
            Ok(NDet::stream(streams.into_iter().flatten()))
        }
    };
    trace_exit!();
    result
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
            Atom::Sym(t) if s == t => Ok(Some(env.clone())),
            // Free variable from term conversion: bind to the literal symbol.
            Atom::Sym(v) if v.starts_with('$') => Ok(Some(env.extend(v, Atom::Sym(s.clone())))),
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

/// Evaluate a list as data: each element is evaluated and collected into a
/// single `Atom::Expr`. This replaces the old "tuple" semantics.
///
/// PeTTa reference: when the head is not a registered fun/1, the list is
/// data — `Out = [HV|AVs]`. In our runtime each element IS evaluated
/// (including nested function calls), then collected into one list atom.
fn eval_data_list(items: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let mut atoms = Vec::with_capacity(items.len());
    for item in items {
        match item {
            Expr::Number(n) => atoms.push(Atom::Num(*n)),
            Expr::Symbol(s) => {
                if s.starts_with('$') {
                    // PeTTa: unbound $vars in a data list stay as Prolog variables
                    // (structural holes). Pattern matching in let/try_match_one
                    // then binds them via computation-in-pattern or direct unification.
                    let val = env.get(s).unwrap_or_else(|| Atom::sym(s));
                    atoms.push(val);
                } else {
                    atoms.push(Atom::sym(s));
                }
            }
            Expr::List(inner) => {
                if inner.is_empty() {
                    atoms.push(Atom::Expr(vec![]));
                } else {
                    let mut results = eval(item, env, funcs)?;
                    match results.next() {
                        Some(val) => atoms.push(val),
                        None => {
                            return Err(
                                "expression produced no results in data list".into(),
                            )
                        }
                    }
                }
            }
        }
    }
    Ok(NDet::single(Atom::Expr(atoms)))
}

// ========================================================================
// Special form evaluators
// ========================================================================

/// Evaluate `(if cond then else)`.
fn eval_if(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "if: expected 3 args (cond then else), got {}",
            args.len()
        ));
    }
    let mut cond_results = eval(&args[0], env, funcs)?;
    let cond = cond_results
        .next()
        .ok_or_else(|| "if: condition produced no results".to_string())?;
    if cond.is_truthy() {
        trace!("if: cond truthy, taking then branch");
        eval(&args[1], env, funcs)
    } else {
        trace!("if: cond falsy, taking else branch");
        eval(&args[2], env, funcs)
    }
}

/// Evaluate `(progn e1 e2 ...)` — sequence.
fn eval_progn(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.is_empty() {
        return Err("progn: expected at least one form".into());
    }
    let mut last: Option<NDet> = None;
    for arg in args {
        last = Some(eval(arg, env, funcs)?);
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
            eval(&args[2], &new_env, funcs).ok()
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
    // Convert to Atom without evaluating (preserve $ vars)
    let atom = expr_to_atom(&args[1]);
    let removed = funcs.space.borrow_mut().remove_atom(&atom)
        .map_err(|e| format!("remove-atom: {}", e))?;
    Ok(NDet::single(if removed {
        Atom::sym("true")
    } else {
        Atom::Sym(String::new())
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
    // Convert pattern expression to a Pattern
    let pattern = Pattern::from_expr(&args[1]);
    // Query the space
    let matches = {
        let space = funcs.space.borrow();
        space.match_atoms(&pattern)
    };
    if matches.is_empty() {
        return Ok(NDet::Single(None)); // empty stream — no match
    }
    // Evaluate body for each match with variable bindings
    let streams: Result<Vec<NDet>, String> = matches
        .into_iter()
        .map(|result| {
            // Extend env with bindings from the match
            let mut match_env = env.clone();
            for (name, val) in &result.bindings {
                match_env = match_env.extend(name, val.clone());
            }
            eval(&args[2], &match_env, funcs)
        })
        .collect();
    Ok(NDet::stream(streams?.into_iter().flatten()))
}

/// Evaluate `(import! space path)` — load a MeTTa file into the space.
///
/// Loads a `.metta` file relative to the current working directory and
/// processes its top-level forms, adding definitions to the space.
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
    // Get file path from args[1] — could be a symbol or string
    let path_str = match &args[1] {
        Expr::Symbol(s) => s.clone(),
        Expr::Number(_) => {
            return Err("import!: file path must be a symbol, not a number".into());
        }
        Expr::List(_) => {
            return Err("import!: file path must be a symbol, not a list".into());
        }
    };
    // Try to load the file — support both .metta and bare paths
    let content = std::fs::read_to_string(&path_str)
        .or_else(|_| {
            let with_ext = format!("{}.metta", path_str);
            std::fs::read_to_string(&with_ext)
        })
        .map_err(|e| format!("import!: cannot read '{}': {}", path_str, e))?;
    let forms = crate::parser::parse_forms(&content)
        .map_err(|e| format!("import!: parse error in '{}': {}", path_str, e))?;
    for form in forms {
        match form {
            TopForm::Definition(expr) => {
                // Store the raw definition atom in the space
                let atom = expr_to_atom(&expr);
                if let Err(e) = funcs.space.borrow_mut().add_atom(&atom) {
                    return Err(format!("import!: add_atom error: {}", e));
                }
                // Register the function clause so it's immediately available
                if let Ok((name, clause)) = crate::compile::compile_definition(&expr) {
                    funcs.add_clause(name, clause.patterns, clause.body);
                }
            }
            TopForm::Runnable(expr) => {
                // PeTTa: load_metta_file processes all forms including !(...) runnables.
                eval(&expr, env, funcs)?;
            }
        }
    }
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(println! arg)` — print a value to stdout (for debugging).
fn eval_println(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("println!: expected 1 arg, got {}", args.len()));
    }
    let mut results = eval(&args[0], env, funcs)?;
    let val = results.next().ok_or_else(|| {
        "println!: argument produced no results".to_string()
    })?;
    println!("{}", val.to_sexpr_string());
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
    match &func_ref.kind {
        FunctionKind::UserDefined { clauses } => {
            let mut results = Vec::new();
            for clause in clauses {
                if clause.patterns.len() != arity {
                    continue;
                }
                // Build concrete arg values: for each position, if the arg expr
                // is an unbound $var, use the clause pattern's literal value;
                // otherwise evaluate the arg normally.
                let mut concrete_args = Vec::with_capacity(arity);
                let mut has_free = false;
                for (i, arg_expr) in items[1..].iter().enumerate() {
                    if let Expr::Symbol(s) = arg_expr {
                        if s.starts_with('$') && env.get(s).is_none() {
                            // Free variable: extract literal from clause pattern
                            match &clause.patterns[i] {
                                Expr::Number(n) => {
                                    concrete_args.push(Atom::Num(*n));
                                    has_free = true;
                                }
                                Expr::Symbol(sym) if !sym.starts_with('$') => {
                                    concrete_args.push(Atom::Sym(sym.clone()));
                                    has_free = true;
                                }
                                _ => {
                                    // Pattern is another $var or nested list —
                                    // can't extract a single literal value
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
                // Call the function with concrete args using direct clause dispatch
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
        FunctionKind::Native { func } => {
            // For each arg, collect all possible values:
            // concrete args → one value; free-var args → recurse to get many values.
            // Then call the native with every combination (cartesian product).
            let native_fn = *func;
            let mut arg_options: Vec<Vec<Atom>> = Vec::with_capacity(arity);
            for arg_expr in &items[1..] {
                match eval(arg_expr, env, funcs) {
                    Ok(nd) => {
                        let vals: Vec<Atom> = nd.collect();
                        if vals.is_empty() { return Ok(vec![]); }
                        arg_options.push(vals);
                    }
                    Err(_) => {
                        let vals = generate_free_var_values(arg_expr, env, funcs)?;
                        if vals.is_empty() { return Ok(vec![]); }
                        arg_options.push(vals);
                    }
                }
            }
            // Cartesian product of all arg options
            let mut combos: Vec<Vec<Atom>> = vec![vec![]];
            for opts in &arg_options {
                combos = combos.into_iter().flat_map(|prefix| {
                    opts.iter().map(move |v| {
                        let mut p = prefix.clone();
                        p.push(v.clone());
                        p
                    }).collect::<Vec<_>>()
                }).collect();
            }
            let mut results = Vec::new();
            for combo in combos {
                if let Ok(mut nd) = native_fn(&combo, funcs) {
                    while let Some(atom) = nd.next() {
                        results.push(atom);
                    }
                }
            }
            if results.is_empty() {
                Err(format!("generator: native {} produced no results", fname))
            } else {
                Ok(results)
            }
        }
    }
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
                let call_expr = Expr::List(vec![Expr::Symbol(fname.clone()), elem_expr]);
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

    // Evaluate the scrutinee
    let mut expr_results = eval(&args[0], env, funcs)?;
    let opt_val = expr_results.next();

    // Get clauses list
    let clauses = match &args[1] {
        Expr::List(items) => items,
        _ => return Err("case: second arg must be a list of (pattern body) pairs".into()),
    };

    // Match on whether scrutinee produced a value — handles the (Empty body) catch case.
    let val = match opt_val {
        None => {
            // Scrutinee produced no results: look for an (Empty body) clause.
            // This is PeTTa's empty-set catch: (case (empty) (... (Empty fallback))).
            for clause in clauses {
                let (pattern, body) = match clause {
                    Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
                    _ => continue,
                };
                if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
                    return eval(body, env, funcs);
                }
            }
            // No Empty clause — propagate emptiness
            return Ok(NDet::stream(std::iter::empty()));
        }
        Some(v) => v,
    };

    // Try each clause in order; skip Empty (only applies to empty scrutinee)
    for clause in clauses {
        let (pattern, body) = match clause {
            Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
            _ => return Err(format!(
                "case: each clause must be (pattern body), got {}",
                clause.to_string()
            )),
        };

        // Skip the Empty catch-all (scrutinee was non-empty)
        if matches!(pattern, Expr::Symbol(s) if s == "Empty") {
            continue;
        }

        // $else always matches as catch-all
        if matches!(pattern, Expr::Symbol(s) if s == "$else") {
            return eval(body, env, funcs);
        }

        // Try pattern match with fresh env
        if let Some(match_env) = try_match_one(pattern, &val, &Env::new(), funcs)? {
            let new_env = prepend_env(match_env, env);
            return eval(body, &new_env, funcs);
        }
    }

    Err(format!(
        "case: no clause matched value {}", val.to_sexpr_string()
    ))
}
