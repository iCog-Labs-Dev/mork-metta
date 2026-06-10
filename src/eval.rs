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
                    "chain" => { trace!("→ special: chain"); return eval_chain(args, env, funcs); }
                    "case" => { trace!("→ special: case"); return eval_case(args, env, funcs); }
                    "foldall" => { trace!("→ special: foldall"); return eval_foldall(args, env, funcs); }
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
    let values: Vec<Atom> = eval(&args[1], env, funcs)?.collect();
    let streams: Vec<NDet> = values
        .into_iter()
        .filter_map(|v| {
            // Fresh match env prevents outer variable capture
            let match_env = try_match_one(pattern, &v, &Env::new()).ok()??;
            let pairs = collect_env_bindings(&match_env);
            let new_env = env.extend_all(&pairs);
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
                let mut val_results = eval(&p[1], &current_env, funcs)?;
                let val = val_results.next().ok_or_else(|| {
                    format!("let*: binding {} produced no value", pattern.to_string())
                })?;
                // Fresh match env prevents outer variable capture
                let match_env = try_match_one(pattern, &val, &Env::new())?
                    .ok_or_else(|| {
                        format!("let*: pattern does not match value: {} vs {}",
                            pattern.to_string(), val.to_sexpr_string())
                    })?;
                let pairs = collect_env_bindings(&match_env);
                current_env = current_env.extend_all(&pairs);
            }
            _ => {
                return Err("let*: each binding must be a list (pattern val)".into())
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
    let fname = match &op_atom {
        Atom::Sym(s) => s.clone(),
        _ => return Err(format!(
            "generator: expected function name, got {}", op_atom.to_sexpr_string()
        )),
    };
    let func = funcs.get(&fname, arity as u8).ok_or_else(|| {
        format!("generator: unknown function {} with {} args", fname, arity)
    })?;
    match &func.kind {
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
                    match try_match_one(pat, arg_val, &match_env)? {
                        Some(new_env) => match_env = new_env,
                        None => { matched = false; break; }
                    }
                }
                if !matched {
                    continue;
                }
                let bindings = collect_env_bindings(&match_env);
                let new_env = env.extend_all(&bindings);
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
        FunctionKind::Native { .. } => {
            Err("generator: native functions don't support free variable resolution".into())
        }
    }
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

    // Evaluate the expression, take first result
    let mut expr_results = eval(&args[0], env, funcs)?;
    let val = expr_results.next().ok_or_else(|| {
        "case: expression produced no results".to_string()
    })?;

    // Get clauses list
    let clauses = match &args[1] {
        Expr::List(items) => items,
        _ => return Err("case: second arg must be a list of (pattern body) pairs".into()),
    };

    // Try each clause in order
    for clause in clauses {
        let (pattern, body) = match clause {
            Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
            _ => return Err(format!(
                "case: each clause must be (pattern body), got {}",
                clause.to_string()
            )),
        };

        // $else always matches as catch-all
        let catch_all = matches!(pattern, Expr::Symbol(s) if s == "$else");
        if catch_all {
            return eval(body, env, funcs);
        }

        // Try pattern match with fresh env
        if let Some(match_env) = try_match_one(pattern, &val, &Env::new())? {
            let pairs = collect_env_bindings(&match_env);
            let new_env = env.extend_all(&pairs);
            return eval(body, &new_env, funcs);
        }
    }

    Err(format!(
        "case: no clause matched value {}", val.to_sexpr_string()
    ))
}
