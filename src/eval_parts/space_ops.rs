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
use crate::eval_parts::core::eval_scope;
use crate::eval_parts::data_list::eval_data_list;
use crate::eval_parts::machine::{self, MachineState, Transition};
use crate::eval_parts::pattern::prepend_env;
use crate::func::{FnTable, NDet};
use crate::parser::{atom_to_expr, Expr};
use crate::space::Pattern;

pub(crate) fn eval_add_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "add-atom: expected (space atom), got {} args",
            args.len()
        ));
    }

    let mut space_results = eval_scope(&args[0], env, funcs)?;
    let space_ref = space_results
        .next()
        .ok_or_else(|| "add-atom: space expression produced no results".to_string())?;

    let atom = crate::eval_parts::special::subst_and_atomize(&args[1], env);
    if matches!(&space_ref, Atom::Sym(name) if name.as_ref() == "&self") {
        let mut state = MachineState::new(None);
        state
            .step(Transition::AddAtom(atom), env, funcs)
            .map_err(|e| format!("add-atom: {}", e))?;
    } else {
        funcs
            .with_resolved_space(&space_ref, |space| space.add_atom(&atom))
            .map_err(|e| format!("add-atom: {}", e))?;
    }

    Ok(NDet::single(Atom::sym("true")))
}

pub(crate) fn eval_remove_atom(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "remove-atom: expected (space atom), got {} args",
            args.len()
        ));
    }

    let mut space_results = eval_scope(&args[0], env, funcs)?;
    let space_ref = space_results
        .next()
        .ok_or_else(|| "remove-atom: space expression produced no results".to_string())?;

    let expr = crate::eval_parts::special::subst_expr_vars(&args[1], env);
    let pattern = crate::space::Pattern::from_expr(&expr);

    let removed_any = if matches!(&space_ref, Atom::Sym(name) if name.as_ref() == "&self") {
        let matches = funcs
            .with_resolved_space(&space_ref, |space| Ok(space.match_atoms(&pattern)))
            .map_err(|e| format!("remove-atom: {}", e))?;

        let mut removed_any = false;
        let mut state = MachineState::new(None);
        for matched in matches {
            state
                .step(Transition::RemAtom(matched.atom.clone()), env, funcs)
                .map_err(|e| format!("remove-atom: {}", e))?;
            removed_any = true;
        }
        removed_any
    } else {
        funcs
            .with_resolved_space(&space_ref, |space| {
                let matches = space.match_atoms(&pattern);
                let mut removed_any = false;
                for matched in matches {
                    if space.remove_atom(&matched.atom)? {
                        removed_any = true;
                    }
                }
                Ok(removed_any)
            })
            .map_err(|e| format!("remove-atom: {}", e))?
    };

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
            let new_items: Vec<Atom> = items
                .iter()
                .map(|a| subst_match_vars(a, bindings))
                .collect();
            Atom::Expr(new_items)
        }
        _ => atom.clone(),
    }
}

fn matches_definition_head(term: &Atom, funcs: &FnTable) -> bool {
    let space = funcs.space.read().unwrap();
    space.get_atoms().iter().any(|atom| match atom {
        Atom::Expr(items)
            if items.len() == 3
                && items[0] == Atom::sym("=")
                && machine::unify(term, &items[1]).is_some() =>
        {
            true
        }
        _ => false,
    })
}

pub(crate) fn eval_transform(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "transform: expected (pattern replacement), got {} args",
            args.len()
        ));
    }

    let pattern = crate::eval_parts::special::subst_and_atomize(&args[0], env);
    let replacement = crate::eval_parts::special::subst_and_atomize(&args[1], env);
    let mut state = MachineState::new(None);
    state.push_input(Atom::Expr(vec![
        Atom::sym("transform"),
        pattern,
        replacement,
    ]));

    while state.should_continue() {
        if !state.input.is_empty() {
            state
                .step(Transition::Transform, env, funcs)
                .map_err(|e| format!("transform: {}", e))?;
            continue;
        }

        if let Some(term) = state.workspace.front().cloned() {
            let transition = if matches_definition_head(&term, funcs) {
                Transition::Chain
            } else {
                Transition::Output
            };
            state
                .step(transition, env, funcs)
                .map_err(|e| format!("transform: {}", e))?;
        }
    }

    Ok(NDet::stream(state.output.into_iter()))
}

fn merge_match_bindings(
    base: &[(String, Atom)],
    extra: &[(String, Atom)],
) -> Option<Vec<(String, Atom)>> {
    let mut merged = base.to_vec();
    for (name, value) in extra {
        if let Some((_, existing)) = merged.iter().find(|(bound, _)| bound == name) {
            if existing != value {
                return None;
            }
        } else {
            merged.push((name.clone(), value.clone()));
        }
    }
    Some(merged)
}

fn collect_match_results(
    space_ref: &Atom,
    pattern_expr: &Expr,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<crate::space::MatchResult>, String> {
    if let Expr::List(items) = pattern_expr {
        if let Some(Expr::Symbol(op)) = items.first() {
            if op == "," {
                let mut bindings_sets: Vec<Vec<(String, Atom)>> = vec![Vec::new()];
                for subpattern in items.iter().skip(1) {
                    let submatches = collect_match_results(space_ref, subpattern, env, funcs)?;
                    let mut next = Vec::new();
                    for bindings in &bindings_sets {
                        for matched in &submatches {
                            if let Some(merged) = merge_match_bindings(bindings, &matched.bindings)
                            {
                                next.push(merged);
                            }
                        }
                    }
                    bindings_sets = next;
                    if bindings_sets.is_empty() {
                        break;
                    }
                }

                return Ok(bindings_sets
                    .into_iter()
                    .map(|bindings| crate::space::MatchResult {
                        atom: Atom::Expr(vec![Atom::sym(",")]),
                        bindings,
                    })
                    .collect());
            }
        }
    }

    let substituted = crate::eval_parts::special::subst_expr_vars(pattern_expr, env);
    let pattern = Pattern::from_expr(&substituted);
    funcs.with_resolved_space(space_ref, |space| Ok(space.match_atoms(&pattern)))
}

pub(crate) fn eval_match(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 3 {
        return Err(format!(
            "match: expected (space pattern body), got {} args",
            args.len()
        ));
    }

    let mut space_results = eval_scope(&args[0], env, funcs)?;
    let space_ref = space_results
        .next()
        .ok_or_else(|| "match: space expression produced no results".to_string())?;

    let matches = collect_match_results(&space_ref, &args[1], env, funcs)
        .map_err(|e| format!("match: {}", e))?;
    let template: Expr = if let Expr::Symbol(s) = &args[2] {
        if s.starts_with('$') {
            crate::eval_parts::special::subst_expr_vars(&args[2], env)
        } else {
            args[2].clone()
        }
    } else {
        crate::eval_parts::special::subst_expr_vars(&args[2], env)
    };

    let eval_one = |mr: &crate::space::MatchResult| -> Result<Vec<Atom>, String> {
        let mut match_env = env.clone();
        for (name, val) in &mr.bindings {
            match_env = match_env.extend(name, val.clone());
        }

        let atoms: Vec<Atom> = eval_scope(&template, &match_env, funcs)?.collect();
        Ok(atoms
            .into_iter()
            .map(|a| subst_match_vars(&a, &mr.bindings))
            .collect())
    };

    let results: Vec<Result<Vec<Atom>, String>> =
        if matches.len() > 1 && crate::eval_parts::data_list::is_pure_expr(&template, funcs) {
            use rayon::prelude::*;
            matches.par_iter().map(eval_one).collect()
        } else {
            matches.iter().map(eval_one).collect()
        };

    let mut result_vecs = Vec::with_capacity(results.len());
    for r in results {
        result_vecs.push(r?);
    }

    Ok(NDet::stream(result_vecs.into_iter().flatten()))
}
