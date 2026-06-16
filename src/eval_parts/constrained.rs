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
use crate::eval_parts::core::eval_scope;
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
    // Unified list dispatcher with relational binding propagation. Resolve the
    // head (carrying its bindings), thread argument bindings left-to-right, then
    // dispatch to: closure application, user-function clauses, native call, or
    // data list. Bindings flow throughout so relational queries terminate.
    if let Expr::List(items) = expr {
        if !items.is_empty() {
            let head = &items[0];
            let args = &items[1..];
            let arity = args.len() as u8;

            // Special forms (collapse, let, case, if, test-as-builtin wrappers,
            // etc.) scope/handle their own variables. The constrained dispatcher
            // would mis-treat them as data, so delegate to the main engine; their
            // results are ground here (no free vars escape the form).
            if let Expr::Symbol(s) = head {
                if crate::eval_parts::cek::is_special_form(s) {
                    let atoms = crate::eval_parts::cek::run(expr, env, funcs)?;
                    return Ok(atoms.into_iter().map(|a| (a, Env::new())).collect());
                }
            }

            // Resolve head candidates (atom, bindings). A plain symbol stays a
            // symbol (dispatch decides fn vs data); $var / compound heads are
            // evaluated.
            let head_cands: Vec<(Atom, Env)> = match head {
                Expr::Symbol(s) if s.starts_with('$') => {
                    vec![(env.get(s).unwrap_or_else(|| Atom::sym(s)), Env::new())]
                }
                Expr::Symbol(s) => vec![(Atom::sym(s), Env::new())],
                other => eval_constrained(other, env, funcs)?,
            };

            let mut out: Vec<(Atom, Env)> = Vec::new();
            for (head_atom, head_binds) in head_cands {
                let henv = prepend_env(head_binds.clone(), env);
                let results: Vec<(Atom, Env)> = match &head_atom {
                    Atom::Closure(c) => {
                        let mut r = Vec::new();
                        for (atom_args, arg_binds) in eval_args_threaded(args, &henv, funcs)? {
                            if let Some(mb) =
                                try_match_clause(&c.params, &atom_args, &Env::new(), funcs)?
                            {
                                let full = prepend_env(mb.clone(), &c.env);
                                for (a, bb) in eval_constrained(&c.body, &full, funcs)? {
                                    let acc = prepend_env(bb, &prepend_env(mb.clone(), &arg_binds));
                                    r.push((a, acc));
                                }
                            }
                        }
                        r
                    }
                    Atom::Sym(name) => {
                        let clauses = lookup_clauses(name, arity, funcs);
                        if !clauses.is_empty() {
                            // Known user function: matched clauses (empty = failure).
                            let combos = eval_args_threaded(args, &henv, funcs)?;
                            apply_clauses(&clauses, &combos, &henv, funcs)?
                        } else if let Some(func) = funcs.get(name, arity) {
                            // Native function: apply per threaded combo.
                            let mut r = Vec::new();
                            for (atom_args, arg_binds) in eval_args_threaded(args, &henv, funcs)? {
                                let nd = match &func.kind {
                                    FunctionKind::Native { func } => func(&atom_args, funcs)?,
                                };
                                for a in nd {
                                    r.push((a, arg_binds.clone()));
                                }
                            }
                            r
                        } else {
                            // Unknown symbol: data list.
                            data_list_threaded(head_atom.clone(), args, &henv, funcs)?
                        }
                    }
                    _ => data_list_threaded(head_atom.clone(), args, &henv, funcs)?,
                };
                for (a, b) in results {
                    out.push((a, prepend_env(b, &head_binds)));
                }
            }
            return Ok(out);
        }
    }
    // Fallback for non-list, non-$ atoms: normal eval, empty bindings.
    // Route through eval_scope so CEK is used when active.
    eval_scope(expr, env, funcs).map(|ndet| ndet.map(|a| (a, Env::new())).collect())
}

/// Look up `(patterns, body)` clauses for `name/arity` from the function cache,
/// falling back to a direct space query (definitions added via `add-atom`).
fn lookup_clauses(name: &str, arity: u8, funcs: &FnTable) -> Vec<crate::func::Clause> {
    if let Some(inner) = funcs.fn_cache.read().unwrap().get(name) {
        if let Some(c) = inner.get(&arity) {
            return c.clone();
        }
    }
    let pat = crate::space::Pattern::Expr(vec![
        crate::space::Pattern::Exact(Atom::sym("=")),
        crate::space::Pattern::Expr(
            std::iter::once(crate::space::Pattern::Exact(Atom::sym(name)))
                .chain((0..arity).map(|_| crate::space::Pattern::Any))
                .collect(),
        ),
        crate::space::Pattern::Any,
    ]);
    let mut cls = Vec::new();
    for m in funcs.space.read().unwrap().match_atoms(&pat) {
        if let Atom::Expr(items) = &m.atom {
            if items.len() == 3 {
                if let Ok(crate::parser::Expr::List(head_items)) =
                    crate::parser::atom_to_expr(&items[1])
                {
                    let patterns: Vec<Expr> = head_items[1..].to_vec();
                    let body = crate::parser::atom_to_expr(&items[2])
                        .unwrap_or_else(|_| Expr::Symbol(items[2].to_sexpr_string()));
                    cls.push(crate::func::Clause { patterns, body });
                }
            }
        }
    }
    cls
}

/// Apply user-function clauses to pre-threaded argument combos, surfacing the
/// query's free-variable bindings (relational propagation) alongside body and
/// argument bindings.
fn apply_clauses(
    clauses: &[crate::func::Clause],
    combos: &[(Vec<Atom>, Env)],
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Atom, Env)>, String> {
    let mut out = Vec::new();
    for (atom_args, arg_bindings) in combos {
        for clause in clauses {
            // Rename the clause's own variables apart (fresh per application) so a
            // recursive body variable (e.g. `$Z`) cannot collide with a caller
            // variable of the same name that is currently in scope. Without this,
            // relational recursion silently loses solutions (Prolog calls this
            // "standardizing apart").
            let clause = rename_clause_apart(clause);
            let mut unif_env = Env::new();
            let mut matched = true;
            for (pat, arg_val) in clause.patterns.iter().zip(atom_args.iter()) {
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
            let mut qbinds = Env::new();
            for arg_atom in atom_args {
                collect_query_var_bindings(arg_atom, &unif_env, &mut qbinds);
            }
            let body_env = prepend_env(unif_env, env);
            for (result_atom, body_bindings) in eval_constrained(&clause.body, &body_env, funcs)? {
                let with_q = prepend_env(qbinds.clone(), arg_bindings);
                let accumulated = prepend_env(body_bindings, &with_q);
                out.push((result_atom, accumulated));
            }
        }
    }
    Ok(out)
}

/// Evaluate a data list (head already an atom) with threaded element bindings.
fn data_list_threaded(
    head_atom: Atom,
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Atom, Env)>, String> {
    let mut out = Vec::new();
    for (atom_args, arg_binds) in eval_args_threaded(args, env, funcs)? {
        let mut v = Vec::with_capacity(atom_args.len() + 1);
        v.push(head_atom.clone());
        v.extend(atom_args);
        out.push((Atom::Expr(v), arg_binds));
    }
    Ok(out)
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

/// Evaluate arguments left-to-right, THREADING bindings: each argument is
/// evaluated in the environment extended by the bindings discovered by the
/// arguments before it. Returns every combination as `(atoms, new_bindings)`
/// where `new_bindings` is relative to `env`.
///
/// This is what gives relational (Prolog-like) behaviour: in
/// `(and (successor $X $Z) (later-in-alphabet $Z $Y))`, the `$Z = c` bound by
/// the first conjunct is visible when evaluating the second. The independent
/// `constrained_cartesian` could not do this (it evaluates every arg in the
/// same env), which let free variables fan out into an unbounded search.
pub(crate) fn eval_args_threaded(
    args: &[Expr],
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<(Vec<Atom>, Env)>, String> {
    let mut combos: Vec<(Vec<Atom>, Env)> = vec![(Vec::new(), Env::new())];
    for arg in args {
        let mut next: Vec<(Vec<Atom>, Env)> = Vec::new();
        for (prefix, acc) in &combos {
            let arg_env = prepend_env(acc.clone(), env);
            for (val, binds) in eval_constrained(arg, &arg_env, funcs)? {
                let merged = prepend_env(binds, acc);
                let mut atoms = prefix.clone();
                atoms.push(val);
                next.push((atoms, merged));
            }
        }
        combos = next;
    }
    Ok(combos)
}

/// Build the cartesian product of per-argument result streams, accumulating bindings.
pub(crate) fn constrained_cartesian(streams: Vec<Vec<(Atom, Env)>>) -> Vec<(Vec<Atom>, Env)> {
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

/// Walk a query argument atom, copying into `out` any binding `unif` assigned to
/// a `$`-variable that appears in the query. Pattern-introduced variables are
/// excluded because they never appear in the query args. Used to surface
/// unification results to sibling expressions (relational binding propagation).
fn collect_query_var_bindings(atom: &Atom, unif: &Env, out: &mut Env) {
    match atom {
        Atom::Sym(s) if s.starts_with('$') => {
            if out.get(s).is_none() {
                if let Some(val) = unif.get(s) {
                    *out = out.extend(s, val);
                }
            }
        }
        Atom::Expr(items) => {
            for it in items {
                collect_query_var_bindings(it, unif, out);
            }
        }
        _ => {}
    }
}

/// Rename a clause's own `$`-variables to globally-fresh names so they cannot
/// capture (collide with) caller variables of the same name that are in scope
/// during relational recursion ("standardizing apart", as in Prolog).
fn rename_clause_apart(clause: &crate::func::Clause) -> crate::func::Clause {
    use std::collections::HashMap;
    let mut map: HashMap<String, String> = HashMap::new();
    let patterns = clause
        .patterns
        .iter()
        .map(|p| rename_vars(p, &mut map))
        .collect();
    let body = rename_vars(&clause.body, &mut map);
    crate::func::Clause { patterns, body }
}

fn rename_vars(expr: &Expr, map: &mut std::collections::HashMap<String, String>) -> Expr {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            let fresh = map.entry(s.clone()).or_insert_with(|| fresh_var(s));
            Expr::Symbol(fresh.clone())
        }
        Expr::List(items) => Expr::List(items.iter().map(|e| rename_vars(e, map)).collect()),
        other => other.clone(),
    }
}

fn fresh_var(original: &str) -> String {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    // Keep the original (minus `$`) for readability; suffix makes it unique.
    format!("{}__r{}", original, n)
}
