/// Space operations: special forms that read or modify the atom space.
///
/// These forms are special — their arguments are NOT pre-evaluated before
/// being passed, preserving `$` variable names in definitions rather than
/// triggering variable lookup errors.
///
/// # Forms
///
/// - `(add-atom space atom)` — add an atom to the space
/// - `(remove-atom space atom)` — remove an atom from the space
/// - `(match space pattern body)` — pattern match atoms in a space

use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::core::eval;
use crate::eval_parts::data_list::eval_data_list;
use crate::eval_parts::pattern::prepend_env;
use crate::func::{FnTable, NDet};
use crate::parser::{atom_to_expr, Expr};
use crate::space::Pattern;

/// Evaluate `(add-atom space atom)` — add an atom to the space.
///
/// This is a special form (not a builtin) because its arguments are NOT
/// evaluated before being passed — PeTTa semantics: `add-atom` receives
/// raw expressions so that `$` variable names in definitions are preserved
/// rather than triggering variable lookup errors.
pub(crate) fn eval_add_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!("add-atom: expected (space atom), got {} args", args.len()));
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
    let atom = crate::eval_parts::special::subst_and_atomize(&args[1], env);
    funcs.space.write().unwrap().add_atom(&atom).map_err(|e| format!("add-atom: {}", e))?;
    // If the atom is a function definition (= head body), also store the bare
    // head atom so `match` can find premise atoms (e.g. (= (f $x) $x) → (f $x)).
    if let Atom::Expr(items) = &atom {
        if items.len() == 3 && items[0] == Atom::sym("=") {
            funcs.space.write().unwrap().add_atom(&items[1])?;
            // Also populate fn_cache
            if let Ok(expr) = crate::parser::atom_to_expr(&atom) {
                if let Ok((name, clause)) = crate::compile::compile_definition(&expr) {
                    funcs.cache_fn(&name, clause.patterns.len() as u8, clause);
                }
            }
        }
    }
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(remove-atom space atom)` — remove an atom from the space.
/// Same special-form treatment as add-atom (arguments not pre-evaluated).
/// Uses pattern matching (like `retract/1`): substitutes env-bound $vars,
/// converts to a pattern, removes all exact matches found.
pub(crate) fn eval_remove_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!("remove-atom: expected (space atom), got {} args", args.len()));
    }
    // Evaluate space reference
    let mut space_results = eval(&args[0], env, funcs)?;
    let _space_ref = space_results.next().ok_or_else(|| {
        "remove-atom: space expression produced no results".to_string()
    })?;
    // In PeTTa, remove-atom uses pattern matching (like `retract/1`).
    // Substitute env-bound $vars first (e.g. $1/$2 bound by an enclosing match),
    // then match the atom as a pattern and remove all exact matches found.
    let expr = crate::eval_parts::special::subst_expr_vars(&args[1], env);
    let pattern = crate::space::Pattern::from_expr(&expr);
    let mut removed_any = false;
    // Hold the lock across snapshot + removal so a concurrent template can't
    // mutate the space between matching an atom and removing it (TOCTOU).
    let removed_atoms: Vec<Atom> = {
        let mut space = funcs.space.write().unwrap();
        let matches = space.match_atoms(&pattern);
        let mut removed = Vec::new();
        for m in matches {
            if let Ok(true) = space.remove_atom(&m.atom) {
                removed_any = true;
                removed.push(m.atom);
            }
        }
        removed
    };
    // Invalidate fn_cache for any removed function definitions.
    for atom in &removed_atoms {
        if let Atom::Expr(items) = atom {
            if items.len() == 3 && items[0] == Atom::sym("=") {
                if let Ok(expr) = crate::parser::atom_to_expr(atom) {
                    if let Ok((name, clause)) = crate::compile::compile_definition(&expr) {
                        funcs.uncache_fn(&name, clause.patterns.len() as u8);
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

/// Substitute match variable bindings into an atom tree.
/// Recursively replaces `Atom::Sym(s)` where `s` is a key in `bindings`
/// with the bound value. This enables match results to carry instantiated
/// bodies that can be re-evaluated without losing variable context.
fn subst_match_vars(atom: &Atom, bindings: &[(String, Atom)]) -> Atom {
    match atom {
        Atom::Sym(s) if s.starts_with('$') => {
            if let Some((_, val)) = bindings.iter().find(|(k, _)| k.as_str() == s.as_ref()) {
                val.clone()
            } else {
                atom.clone()
            }
        }
        Atom::Expr(items) => {
            let new_items: Vec<Atom> = items.iter()
                .map(|a| subst_match_vars(a, bindings))
                .collect();
            Atom::Expr(new_items)
        }
        _ => atom.clone(),
    }
}

/// Evaluate `(match space pattern body)` — pattern match atoms in a space.
///
/// Evaluates `space` to get the space reference, converts `pattern` to a
/// `Pattern`, queries the space for matching atoms, then evaluates `body`
/// once per match with variables bound from the pattern.
///
/// PeTTa semantics: `match(Space, Pattern, Out, Out)` — matches atoms in
/// the space, binds variables from the pattern to the matched atom.
pub(crate) fn eval_match(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
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
        let substituted = crate::eval_parts::special::subst_expr_vars(&args[1], env);
        Pattern::from_expr(&substituted)
    };
    // Query the space — brief lock, collect all results, then release.
    let matches = funcs.space.read().unwrap().match_atoms(&pattern);
    if matches.is_empty() {
        return Ok(NDet::Single(None)); // empty stream — no match
    }
    // Template: if args[2] is a $var bound in env, resolve to atom then convert to
    // expr so that match bindings (e.g. $1 → 1) are applied when evaluating it.
    let template: Expr = if let Expr::Symbol(s) = &args[2] {
        if s.starts_with('$') {
            if let Some(atom) = env.get(s) {
                crate::parser::atom_to_expr(&atom)?
            } else {
                args[2].clone()
            }
        } else {
            args[2].clone()
        }
    } else {
        args[2].clone()
    };
    // Evaluate the template once per match. Parallel only when the template is
    // pure — impure templates (add-atom/remove-atom/nested match/IO) must run
    // sequentially in match order, otherwise side effects interleave between
    // workers and per-op Mutex atomicity does not protect the sequences.
    let eval_one = |mr: &crate::space::MatchResult| -> Result<Vec<Atom>, String> {
        let mut match_env = env.clone();
        for (name, val) in &mr.bindings {
            match_env = match_env.extend(name, val.clone());
        }
        let atoms: Vec<Atom> = eval(&template, &match_env, funcs)?.collect();
        // Substitute match bindings into each result atom so that definition
        // body variables (e.g. $a, $b in (= (f $L $a $b) body)) are replaced
        // with their matched values. This allows match + eval chains to work.
        Ok(atoms.into_iter().map(|a| subst_match_vars(&a, &mr.bindings)).collect())
    };
    let results: Vec<Result<Vec<Atom>, String>> =
        if matches.len() > 1 && crate::eval_parts::data_list::is_pure_expr(&template, funcs) {
            use rayon::prelude::*;
            matches.par_iter().map(eval_one).collect()
        } else {
            matches.iter().map(eval_one).collect()
        };
    // Propagate the first error instead of silently dropping failed branches.
    let mut result_vecs = Vec::with_capacity(results.len());
    for r in results {
        result_vecs.push(r?);
    }
    Ok(NDet::stream(result_vecs.into_iter().flatten()))
}
