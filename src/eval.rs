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

use crate::atom::Atom;
use crate::env::Env;
use crate::func::{FnTable, FunctionKind, NDet};
use crate::parser::{atom_to_expr, expr_to_atom, Expr};
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
                    "quote" => { trace!("→ special: quote"); return eval_quote(args); }
                    "eval" => { trace!("→ special: eval"); return eval_eval(args, env, funcs); }
                    "superpose" => { trace!("→ special: superpose"); return eval_superpose(args, env, funcs); }
                    "collapse" => { trace!("→ special: collapse"); return eval_collapse(args, env, funcs); }
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
    // Case 1: plain (non-$) symbol — either a known function or a data list.
    if let Expr::Symbol(s) = op {
        if !s.starts_with('$') {
            // SAFETY: args.len() is the number of parsed function arguments —
            // never exceeds practical limits (<10 in real usage). The cast to
            // u8 is safe because no MeTTa function has >255 args.
            if funcs.get(s, args.len() as u8).is_some() {
                return call_function(s, args, env, funcs);
            }
            // Unknown plain symbol → data list (single Expr atom)
            trace!("→ unknown symbol '{}', treating as data list", s);
            return eval_data_list(all_items, env, funcs);
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
        if funcs.get(fname, args.len() as u8).is_some() {
            return call_function(fname, args, env, funcs);
        }
    }

    // Fallback: data list — collect evaluated elements into one Expr atom.
    trace!("→ fallback: data list");
    eval_data_list(all_items, env, funcs)
}

/// Call a known function with the given arguments.
/// Arguments are evaluated deterministically (first result of each).
fn call_function(
    op_name: &str,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<NDet, String> {
    trace_enter!("call: {} ({} args)", op_name, args.len());
    // SAFETY: args.len() is small (no function has >255 args). See try_call_or_data.
    let func = funcs.get(op_name, args.len() as u8).ok_or_else(|| {
        format!("internal: function {} with {} args disappeared from table",
            op_name, args.len())
    })?;
    // Evaluate arguments (take first result of each)
    let mut arg_vals = Vec::with_capacity(args.len());
    for (i, arg) in args.iter().enumerate() {
        let mut results = eval(arg, env, funcs)?;
        let val = results.next().ok_or_else(|| {
            format!("{}: argument {} produced no results", op_name, i + 1)
        })?;
        arg_vals.push(val);
    }
    let arg_strs: Vec<String> = arg_vals.iter().map(|a| a.to_sexpr_string()).collect();
    trace!("{} args: [{}]", op_name, arg_strs.join(", "));
    let result = match &func.kind {
        FunctionKind::Native { func: f } => f(&arg_vals, funcs),
        FunctionKind::UserDefined { clauses } => {
            let mut streams: Vec<NDet> = Vec::new();
            for clause in clauses {
                match try_match_clause(&clause.patterns, &arg_vals, env)? {
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
                    arg_strs.join(", ")
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
) -> Result<Option<Env>, String> {
    if patterns.len() != args.len() {
        return Ok(None);
    }
    // Use a fresh env for pattern matching so outer bindings don't interfere
    // with variable capture in recursive calls (e.g., fib($N) called with
    // outer $N=30 should match $N=29, not fail).
    let mut match_env = Env::new();
    for (pat, arg) in patterns.iter().zip(args.iter()) {
        match try_match_one(pat, arg, &match_env)? {
            Some(new_env) => match_env = new_env,
            None => return Ok(None),
        }
    }
    // Extend the calling env with bindings from the match
    let bindings = collect_env_bindings(&match_env);
    Ok(Some(env.extend_all(&bindings)))
}
/// Collect all bindings from an environment into a Vec.
fn collect_env_bindings(env: &Env) -> Vec<(String, Atom)> {
    let mut result = Vec::new();
    let mut current = env;
    loop {
        match current {
            Env::Empty => break,
            Env::Cons { name, value, next } => {
                result.push((name.to_string(), value.clone()));
                current = next;
            }
        }
    }
    result
}
/// Match a single pattern against a single atom.
///
/// Pattern kinds:
/// - `$var` (symbol starting with `$`): binds to the atom, or checks
///   equality if already bound (non-linear patterns).
/// - `Num(n)`: matches only `Atom::Num(n)`.
/// - `Sym(s)`: matches only `Atom::Sym(t)` where `s == t`.
/// - `List(items)`: structural match — recursively matches each element
///   against the corresponding element in `Atom::Expr(elems)`.
fn try_match_one(
    pattern: &Expr,
    atom: &Atom,
    env: &Env,
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
            _ => Ok(None),
        },
        Expr::Symbol(s) => match atom {
            Atom::Sym(t) if s == t => Ok(Some(env.clone())),
            _ => Ok(None),
        },
        Expr::List(items) => match atom {
            Atom::Expr(elems) => {
                if items.len() != elems.len() {
                    return Ok(None);
                }
                let mut current = env.clone();
                for (pat, arg) in items.iter().zip(elems.iter()) {
                    match try_match_one(pat, arg, &current)? {
                        Some(new_env) => current = new_env,
                        None => return Ok(None),
                    }
                }
                Ok(Some(current))
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
                    let val = env.get(s).ok_or_else(|| {
                        format!("unbound variable: {}", s)
                    })?;
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

/// Evaluate `(let $var value body)` — nondeterministic variable binding.
fn eval_let(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "let: expected ($var value body), got {} args",
            args.len()
        ));
    }
    let var_name = match &args[0] {
        Expr::Symbol(s) if s.starts_with('$') => s.clone(),
        _ => {
            return Err(
                "let: first argument must be a $variable (pattern let not supported)"
                    .into(),
            )
        }
    };
    let values: Vec<Atom> = eval(&args[1], env, funcs)?.collect();
    let streams: Vec<NDet> = values
        .into_iter()
        .filter_map(|v| {
            let new_env = env.extend(&var_name, v);
            eval(&args[2], &new_env, funcs).ok()
        })
        .collect();
    Ok(NDet::stream(streams.into_iter().flatten()))
}

/// Evaluate `(let* ((x a) (y b) ...) body)` — sequential `let`.
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
                "let*: first arg must be a list of ($var val) pairs".into(),
            )
        }
    };
    let mut current_env = env.clone();
    for pair in bindings {
        match pair {
            Expr::List(p) if p.len() == 2 => {
                let var_name = match &p[0] {
                    Expr::Symbol(s) if s.starts_with('$') => s.clone(),
                    _ => {
                        return Err(
                            "let*: each binding must be ($var val) with $var".into(),
                        )
                    }
                };
                let mut val_results = eval(&p[1], &current_env, funcs)?;
                let val = val_results.next().ok_or_else(|| {
                    format!("let*: binding {} produced no value", var_name)
                })?;
                current_env = current_env.extend(&var_name, val);
            }
            _ => {
                return Err("let*: each binding must be a list ($var val)".into())
            }
        }
    }
    eval(&args[1], &current_env, funcs)
}

/// Evaluate `(quote expr)` — return expression as data.
fn eval_quote(args: &[Expr]) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("quote: expected 1 arg, got {}", args.len()));
    }
    let atom = expr_to_atom(&args[0]);
    Ok(NDet::single(atom))
}

/// Evaluate `(eval expr)` — evaluate, convert result to code, evaluate again.
fn eval_eval(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 1 {
        return Err(format!("eval: expected 1 arg, got {}", args.len()));
    }
    let mut inner_results = eval(&args[0], env, funcs)?;
    let atom_val = inner_results
        .next()
        .ok_or_else(|| "eval: inner expression produced no results".to_string())?;
    let expr = atom_to_expr(&atom_val)?;
    eval(&expr, env, funcs)
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
