//! Continuation application logic.
//!
//! This module resumes suspended frames with child results and determines the
//! next machine actions required to continue evaluation.

use super::budget::{atoms_of, plain, ResultSet};
use super::frame::Frame;
use super::state::Transition;
use super::task::Task;
use crate::atom::Atom;
use crate::env::Env;
use crate::func::FnTable;
use crate::parser::Expr;
use std::sync::Arc;

/// Pop the top `n` result sets from the value stack.
///
/// The returned result sets preserve push order, with the oldest of the popped
/// entries appearing first.
pub(crate) fn pop_n(values: &mut Vec<ResultSet>, n: usize) -> Vec<ResultSet> {
    let split_at = values.len() - n;
    values.split_off(split_at)
}

/// Build the cartesian product of a list of value lists.
pub(crate) fn cartesian_product(options: &[Vec<Atom>]) -> Vec<Vec<Atom>> {
    if options.is_empty() {
        return vec![Vec::new()];
    }

    let mut result = vec![Vec::new()];
    for option in options {
        let mut next = Vec::with_capacity(result.len() * option.len());
        for prefix in &result {
            for value in option {
                let mut combination = prefix.clone();
                combination.push(value.clone());
                next.push(combination);
            }
        }
        result = next;
    }
    result
}

/// Threaded cartesian product of result sets, preserving environments.
///
/// Each result set is a list of (Atom, Env) pairs. This produces all combinations
/// of atoms, threading the environments left-to-right: the env from the i-th arg
/// is accumulated before processing the (i+1)-th arg.
///
/// This is what enables relational (Prolog-like) behaviour where bindings
/// discovered in one argument are visible in subsequent arguments.
fn threaded_combinations(sets: &[ResultSet]) -> Vec<(Vec<Atom>, Env)> {
    let mut combos = vec![(Vec::new(), Env::new())];
    for rs in sets {
        let mut next = Vec::new();
        for (prefix, acc_env) in &combos {
            for (atom, atom_env) in rs {
                let mut atoms = prefix.clone();
                atoms.push(atom.clone());
                let merged = crate::eval::shared::pattern::prepend_env(atom_env.clone(), acc_env);
                next.push((atoms, merged));
            }
        }
        combos = next;
    }
    combos
}

/// Apply a continuation frame to the current value stack.
pub(crate) fn apply_frame(
    frame: Frame,
    funcs: &FnTable,
    work: &mut Vec<Task>,
    vals: &mut Vec<ResultSet>,
) -> Result<(), String> {
    match frame {
        Frame::Gather { n } => {
            let mut out = Vec::new();
            for result_set in pop_n(vals, n) {
                out.extend(result_set);
            }
            vals.push(out);
            Ok(())
        }
        Frame::IfGather { had_bindings, n } => {
            let mut out = Vec::new();
            for result_set in pop_n(vals, n) {
                out.extend(atoms_of(&result_set));
            }
            let result = match out.len() {
                0 => Vec::new(),
                1 => plain(out),
                _ if had_bindings => plain(vec![Atom::Expr(out)]),
                _ => plain(out),
            };
            vals.push(result);
            Ok(())
        }
        Frame::MergeEnv { env } => {
            let rs = pop_n(vals, 1).pop().unwrap();
            let merged: Vec<(Atom, Env)> = rs
                .into_iter()
                .map(|(atom, result_env)| {
                    let merged = crate::eval::shared::pattern::prepend_env(env.clone(), &result_env);
                    (atom, merged)
                })
                .collect();
            vals.push(merged);
            Ok(())
        }
        Frame::CaseSelect { clauses, env } => {
            let scrutinee_rs = pop_n(vals, 1).pop().unwrap();
            if scrutinee_rs.is_empty() {
                for clause in clauses.iter() {
                    if let Expr::List(items) = clause {
                        if items.len() == 2 {
                            if matches!(&items[0], Expr::Symbol(s) if s == "Empty") {
                                work.push(Task::Eval {
                                    expr: Arc::new(items[1].clone()),
                                    env: env.clone(),
                                });
                                return Ok(());
                            }
                        }
                    }
                }
                vals.push(Vec::new());
                return Ok(());
            }
            let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
            for (value, _) in &scrutinee_rs {
                let mut selected = None;
                for clause in clauses.iter() {
                    let (pattern, body) = match clause {
                        Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
                        _ => {
                            return Err(format!(
                                "case: each clause must be (pattern body), got {}",
                                clause.to_string()
                            ))
                        }
                    };
                    if matches!(pattern, Expr::Symbol(symbol) if symbol == "Empty") {
                        continue;
                    }
                    if matches!(pattern, Expr::Symbol(symbol) if symbol == "$else") {
                        selected = Some((Arc::new(body.clone()), env.clone()));
                        break;
                    }
                    if let Some(match_env) = crate::eval::shared::pattern::try_match_one(
                        pattern,
                        value,
                        &Env::new(),
                        funcs,
                    )? {
                        let body_env = crate::eval::shared::env::prepend_chain(match_env, &env);
                        selected = Some((Arc::new(body.clone()), body_env));
                        break;
                    }
                }
                if let Some(branch) = selected {
                    branches.push(branch);
                } else {
                    return Err(format!(
                        "case: no clause matched value {}",
                        value.to_sexpr_string()
                    ));
                }
            }
            if branches.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: branches.len() }));
            for (expr, body_env) in branches.into_iter().rev() {
                work.push(Task::Eval {
                    expr,
                    env: body_env,
                });
            }
            Ok(())
        }
        Frame::LetMatch { pattern, body, env } => {
            let value_rs = pop_n(vals, 1).pop().unwrap();

            let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
            for (value, _) in &value_rs {
                if let Ok(Some(matched)) =
                    crate::eval::shared::pattern::try_match_one(&pattern, value, &Env::new(), funcs)
                {
                    let body_env = crate::eval::shared::env::prepend_chain(matched, &env);
                    branches.push((Arc::clone(&body), body_env));
                }
            }
            if branches.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: branches.len() }));
            for (expr, body_env) in branches.into_iter().rev() {
                work.push(Task::Eval {
                    expr,
                    env: body_env,
                });
            }
            Ok(())
        }
        Frame::FoldlInit => {
            // Pop 3 result sets: list_rs, acc_rs, func_rs (pushed in reverse)
            let mut three = pop_n(vals, 3);
            let func_rs = three.pop().unwrap();
            let acc_rs = three.pop().unwrap();
            let list_rs = three.pop().unwrap();
            let func = func_rs.into_iter().next().map(|(a, _)| a)
                .ok_or_else(|| "foldl-atom: func arg produced no result".to_string())?;
            let acc = acc_rs.into_iter().next().map(|(a, _)| a)
                .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
            let items: Vec<crate::atom::Atom> = match list_rs.into_iter().next().map(|(a, _)| a) {
                Some(crate::atom::Atom::Expr(v)) => v,
                Some(other) => vec![other],
                None => return Err("foldl-atom: list arg produced no result".to_string()),
            };
            if items.is_empty() {
                vals.push(super::budget::plain(vec![acc]));
                return Ok(());
            }
            let item = items[0].clone();
            let func_expr = crate::parser::atom_to_expr(&func)
                .unwrap_or(crate::parser::Expr::Symbol(func.to_sexpr_string()));
            let acc_expr = crate::parser::atom_to_expr(&acc)
                .unwrap_or(crate::parser::Expr::Symbol(acc.to_sexpr_string()));
            let item_expr = crate::parser::atom_to_expr(&item)
                .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
            let call = crate::parser::Expr::List(vec![func_expr, acc_expr, item_expr]);
            work.push(Task::Apply(Frame::FoldlAtom {
                items: Arc::new(items),
                index: 1,
                acc,
                func,
            }));
            work.push(Task::Eval {
                expr: Arc::new(call),
                env: crate::env::Env::new(),
            });
            Ok(())
        }
        Frame::Println => {
            let result = pop_n(vals, 1).pop().unwrap();
            for (atom, _) in &result {
                eprintln!("{}", atom.to_sexpr_string());
            }
            vals.push(result);
            Ok(())
        }
        Frame::ImportFile { path, env } => {
            let space_rs = pop_n(vals, 1).pop().unwrap();
            let _space_ref = space_rs
                .into_iter()
                .next()
                .map(|(a, _)| a)
                .unwrap_or_else(|| crate::atom::Atom::sym("&self"));
            let import_dir = funcs.import_dir.lock().unwrap().clone();
            let resolved = crate::eval::io::resolve_import_path(&path, &import_dir)
                .ok_or_else(|| {
                    format!(
                        "import!: cannot find '{}' (searched CWD and '{}')",
                        path,
                        import_dir.display()
                    )
                })?;
            let new_dir = resolved
                .parent()
                .unwrap_or(std::path::Path::new("."))
                .to_path_buf();
            let prev_dir = std::mem::replace(&mut *funcs.import_dir.lock().unwrap(), new_dir);
            let atoms = crate::eval::io::load_metta_file(&resolved, &env, funcs)?;
            *funcs.import_dir.lock().unwrap() = prev_dir;
            vals.push(super::budget::plain(atoms));
            Ok(())
        }
        Frame::FoldlAtom { items, index, acc, func } => {
            let step_rs = pop_n(vals, 1).pop().unwrap();
            let new_acc = step_rs
                .into_iter()
                .next()
                .map(|(a, _)| a)
                .unwrap_or(acc);
            if index >= items.len() {
                vals.push(super::budget::plain(vec![new_acc]));
                return Ok(());
            }
            let item = items[index].clone();
            let func_expr = crate::parser::atom_to_expr(&func)
                .unwrap_or(crate::parser::Expr::Symbol(func.to_sexpr_string()));
            let acc_expr = crate::parser::atom_to_expr(&new_acc)
                .unwrap_or(crate::parser::Expr::Symbol(new_acc.to_sexpr_string()));
            let item_expr = crate::parser::atom_to_expr(&item)
                .unwrap_or(crate::parser::Expr::Symbol(item.to_sexpr_string()));
            let call = crate::parser::Expr::List(vec![func_expr, acc_expr, item_expr]);
            work.push(Task::Apply(Frame::FoldlAtom {
                items,
                index: index + 1,
                acc: new_acc,
                func,
            }));
            work.push(Task::Eval {
                expr: Arc::new(call),
                env: crate::env::Env::new(),
            });
            Ok(())
        }
        Frame::LetStarBind {
            bindings,
            bind_index,
            body,
            env,
        } => {
            let value_rs = pop_n(vals, 1).pop().unwrap();

            let (pattern, _) =
                crate::eval::forms::control::let_star_binding(&bindings, bind_index)?;
            enum Branch {
                Next {
                    next_index: usize,
                    value_expr: Expr,
                    env: Env,
                },
                Final {
                    env: Env,
                },
            }
            let mut branches = Vec::new();
            for (value, _) in &value_rs {
                if let Ok(Some(matched)) =
                    crate::eval::shared::pattern::try_match_one(pattern, value, &Env::new(), funcs)
                {
                    let next_env = crate::eval::shared::env::prepend_chain(matched, &env);
                    if bind_index + 1 < bindings.len() {
                        let (_, value_expr) = crate::eval::forms::control::let_star_binding(
                            &bindings,
                            bind_index + 1,
                        )?;
                        branches.push(Branch::Next {
                            next_index: bind_index + 1,
                            value_expr: value_expr.clone(),
                            env: next_env,
                        });
                    } else {
                        branches.push(Branch::Final { env: next_env });
                    }
                }
            }
            if branches.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: branches.len() }));
            for branch in branches.into_iter().rev() {
                match branch {
                    Branch::Next {
                        next_index,
                        value_expr,
                        env,
                    } => {
                        work.push(Task::Apply(Frame::LetStarBind {
                            bindings: Arc::clone(&bindings),
                            bind_index: next_index,
                            body: Arc::clone(&body),
                            env: env.clone(),
                        }));
                        work.push(Task::Eval {
                            expr: Arc::new(value_expr),
                            env,
                        });
                    }
                    Branch::Final { env } => {
                        work.push(Task::Eval {
                            expr: Arc::clone(&body),
                            env,
                        });
                    }
                }
            }
            Ok(())
        }
        Frame::SpaceMatch { pattern, body, env } => {
            let space_rs = pop_n(vals, 1).pop().unwrap();
            // Substitute body expression variables from env for indirect variable
            // references (e.g. body=$ret where $ret→Sym($1)).
            let body = crate::eval::shared::subst::subst_expr_vars(&body, &env);
            let mut branches: Vec<(Arc<Expr>, Env)> = Vec::new();
            for (space_ref, _) in &space_rs {
                let matches =
                    crate::space::query::collect_match_results(funcs, space_ref, &pattern, &env)?;
                for matched in matches {
                    let body_env = crate::eval::shared::env::bind_all(&env, &matched.bindings);
                    branches.push((Arc::new(body.clone()), body_env));
                }
            }
            if branches.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: branches.len() }));
            for (expr, body_env) in branches.into_iter().rev() {
                work.push(Task::Eval {
                    expr,
                    env: body_env,
                });
            }
            Ok(())
        }
        Frame::SpaceAdd { atom, env } => {
            let space_rs = pop_n(vals, 1).pop().unwrap();
            let atom = crate::eval::shared::subst::subst_and_atomize(&atom, &env);
            if space_rs.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: space_rs.len() }));
            for (space_ref, _) in space_rs.into_iter().rev() {
                work.push(Task::Transition(Transition::AddAtom {
                    space_ref,
                    atom: atom.clone(),
                }));
            }
            Ok(())
        }
        Frame::SpaceRemove { atom, env } => {
            let space_rs = pop_n(vals, 1).pop().unwrap();
            let atom = crate::eval::shared::subst::subst_and_atomize(&atom, &env);
            if space_rs.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: space_rs.len() }));
            for (space_ref, _) in space_rs.into_iter().rev() {
                work.push(Task::Transition(Transition::RemAtom {
                    space_ref,
                    atom: atom.clone(),
                }));
            }
            Ok(())
        }
        Frame::MutexEnter { body, env } => {
            let mutex_rs = pop_n(vals, 1).pop().unwrap();
            if mutex_rs.is_empty() {
                vals.push(Vec::new());
                return Ok(());
            }
            work.push(Task::Apply(Frame::Gather { n: mutex_rs.len() }));
            for (mutex_name, _) in mutex_rs.into_iter().rev() {
                work.push(Task::Transition(Transition::WithMutex {
                    mutex_name: mutex_name.to_sexpr_string(),
                    body: Arc::clone(&body),
                    env: env.clone(),
                }));
            }
            Ok(())
        }
        Frame::WithinWrap => {
            let result_set = pop_n(vals, 1).pop().unwrap();
            let atoms = atoms_of(&result_set);
            if atoms.is_empty() {
                return Err("within: expression produced no results".into());
            }
            let wrapped = Atom::Expr(std::iter::once(Atom::sym("within")).chain(atoms).collect());
            vals.push(plain(vec![wrapped]));
            Ok(())
        }
        Frame::CollapseGather => {
            let result_set = pop_n(vals, 1).pop().unwrap();
            vals.push(plain(vec![Atom::Expr(atoms_of(&result_set))]));
            Ok(())
        }
        Frame::OnceCut => {
            let result_set = pop_n(vals, 1).pop().unwrap();
            match result_set.into_iter().next() {
                Some(pair) => vals.push(vec![pair]),
                None => vals.push(Vec::new()),
            }
            Ok(())
        }
        Frame::ChainBind {
            args,
            pair_index,
            env,
        } => {
            let result_set = pop_n(vals, 1).pop().unwrap();
            let value = result_set
                .into_iter()
                .next()
                .map(|(atom, _)| atom)
                .ok_or_else(|| {
                    format!("chain: expression {} produced no results", pair_index * 2)
                })?;
            let var = &args[pair_index * 2 + 1];
            let var_name = match var {
                Expr::Symbol(symbol) if symbol.starts_with('$') => symbol.clone(),
                _ => {
                    return Err(format!(
                        "chain: arg {} must be a $variable, got {}",
                        pair_index * 2 + 1,
                        var.to_string()
                    ))
                }
            };
            let next_env = crate::eval::forms::control::bind_value(&env, &var_name, value);
            let pairs = args.len() / 2;
            if pair_index + 1 < pairs {
                let next_pair = pair_index + 1;
                work.push(Task::Apply(Frame::ChainBind {
                    args: Arc::clone(&args),
                    pair_index: next_pair,
                    env: next_env.clone(),
                }));
                work.push(Task::Eval {
                    expr: Arc::new(args[next_pair * 2].clone()),
                    env: next_env,
                });
            } else {
                work.push(Task::Eval {
                    expr: Arc::new(args[args.len() - 1].clone()),
                    env: next_env,
                });
            }
            Ok(())
        }
        Frame::SuperposeUnpack => {
            let result_set = pop_n(vals, 1).pop().unwrap();
            let first = result_set
                .into_iter()
                .next()
                .map(|(atom, _)| atom)
                .ok_or_else(|| "superpose: argument produced no results".to_string())?;
            match first {
                Atom::Expr(elements) => vals.push(plain(elements)),
                other => vals.push(plain(vec![other])),
            }
            Ok(())
        }
        Frame::DataListWithHead { head, n_tail } => {
            let tail_rs = pop_n(vals, n_tail);
            let tail_atoms: Vec<Vec<Atom>> = tail_rs.iter().map(atoms_of).collect();
            if tail_atoms.iter().any(|element| element.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            let combos = cartesian_product(&tail_atoms);
            let lists = combos
                .into_iter()
                .map(|tail_values| {
                    let mut atoms = Vec::with_capacity(tail_values.len() + 1);
                    atoms.push(head.clone());
                    atoms.extend(tail_values);
                    Atom::Expr(atoms)
                })
                .collect();
            vals.push(plain(lists));
            Ok(())
        }
        Frame::DataList { n } => {
            let per_elem_rs = pop_n(vals, n);
            let per_elem: Vec<Vec<Atom>> = per_elem_rs.iter().map(atoms_of).collect();
            if per_elem.iter().any(|element| element.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            let combos = cartesian_product(&per_elem);
            let lists: Vec<Atom> = combos.into_iter().map(Atom::Expr).collect();
            vals.push(plain(lists));
            Ok(())
        }
        Frame::ApplyHead { arity, env } => {
            let head_rs = pop_n(vals, 1).pop().unwrap();
            let arg_sets = pop_n(vals, arity);
            // Try each head candidate; use first that matches
            for (head_atom, _head_env) in &head_rs {
                match head_atom {
                    Atom::Sym(name) => {
                        // Dispatch as a named function call
                        let arg_options: Vec<Vec<Atom>> = arg_sets.iter().map(atoms_of).collect();
                        if arg_options.iter().any(|values| values.is_empty()) {
                            vals.push(Vec::new());
                            return Ok(());
                        }
                        // Try native
                        if let Some(function) = funcs.get(name, arity as u8) {
                            if let crate::func::FunctionKind::Native { func } = &function.kind {
                                let combos = cartesian_product(&arg_options);
                                let mut results = Vec::new();
                                for slice in &combos {
                                    match func(slice, funcs) {
                                        Ok(nd) => results.extend(nd),
                                        Err(e) => return Err(e),
                                    }
                                }
                                vals.push(plain(results));
                                return Ok(());
                            }
                        }
                        // Try user clauses
                        if let Some(clauses) =
                            crate::eval::forms::query::lookup_user_clauses(name, arity as u8, funcs)
                        {
                            let combos_with_envs = threaded_combinations(&arg_sets);
                            let mut bodies: Vec<(Arc<Expr>, Env, i64)> = Vec::new();
                            for (combo, combo_env) in &combos_with_envs {
                                for (patterns, body) in &clauses {
                                    if let Some((body_env, subst_cost)) =
                                        crate::eval::forms::query::match_clause(patterns, combo, combo_env, funcs)
                                    {
                                        bodies.push((Arc::new(body.clone()), body_env, subst_cost));
                                    }
                                }
                            }
                            if !bodies.is_empty() {
                                let mut out = Vec::new();
                                for (body, body_env, _) in bodies {
                                    let body_rs = super::step::run_rs(body, body_env, funcs, &mut None)?;
                                    out.extend(body_rs);
                                }
                                let merged: Vec<Atom> = out.into_iter().map(|(a, _)| a).collect();
                                vals.push(plain(merged));
                                return Ok(());
                            }
                        }
                        // Fall through to data list
                    }
                    Atom::Closure(c) => {
                        let clauses: Vec<(Vec<Expr>, Expr)> =
                            vec![(c.params.clone(), c.body.clone())];
                        let combos_with_envs = threaded_combinations(&arg_sets);
                        let mut bodies: Vec<(Arc<Expr>, Env, i64)> = Vec::new();
                        for (combo, combo_env) in &combos_with_envs {
                            for (patterns, body) in &clauses {
                                if let Some((body_env, subst_cost)) =
                                    crate::eval::forms::query::match_clause(patterns, combo, combo_env, funcs)
                                {
                                    bodies.push((Arc::new(body.clone()), body_env, subst_cost));
                                }
                            }
                        }
                        if !bodies.is_empty() {
                            let mut out = Vec::new();
                            for (body, body_env, _) in bodies {
                                let body_rs = super::step::run_rs(body, body_env, funcs, &mut None)?;
                                out.extend(body_rs);
                            }
                            let merged: Vec<Atom> = out.into_iter().map(|(a, _)| a).collect();
                            vals.push(plain(merged));
                            return Ok(());
                        }
                    }
                    _ => {}
                }
            }
            // Fallback: construct as data list
            let per_elem: Vec<Vec<Atom>> = arg_sets.iter().map(atoms_of).collect();
            if per_elem.iter().any(|e| e.is_empty()) {
                vals.push(Vec::new());
                return Ok(());
            }
            // Include head in data list
            let all_atoms: Vec<Vec<Atom>> = std::iter::once(
                head_rs.into_iter().map(|(a, _)| a).collect()
            ).chain(per_elem).collect();
            let combos = cartesian_product(&all_atoms);
            let lists: Vec<Atom> = combos.into_iter().map(Atom::Expr).collect();
            vals.push(plain(lists));
            Ok(())
        }
        Frame::Call {
            head,
            arity,
            env,
            prebound_args,
        } => {
            let arg_sets = if let Some(prebound_args) = prebound_args {
                let eager_count = prebound_args.iter().filter(|slot| slot.is_none()).count();
                let mut eager_sets = pop_n(vals, eager_count).into_iter();
                prebound_args
                    .into_iter()
                    .map(|slot| slot.unwrap_or_else(|| eager_sets.next().unwrap()))
                    .collect()
            } else {
                pop_n(vals, arity)
            };
            let arg_options: Vec<Vec<Atom>> = arg_sets.iter().map(atoms_of).collect();

            match head {
                super::task::Head::Native(f) => {
                    if arg_options.iter().any(|values| values.is_empty()) {
                        return Err("argument produced no results".to_string());
                    }
                    let combos = cartesian_product(&arg_options);
                    let mut results = Vec::new();
                    let mut last_err = None;
                    for slice in &combos {
                        match f(slice, funcs) {
                            Ok(nd) => results.extend(nd),
                            Err(err) => last_err = Some(err),
                        }
                    }
                    if results.is_empty() {
                        if let Some(err) = last_err {
                            return Err(err);
                        }
                    }
                    vals.push(plain(results));
                    Ok(())
                }
                super::task::Head::User {
                    name: _,
                    clauses,
                    lazy_mask: _,
                } => {
                    let combos_with_envs = threaded_combinations(&arg_sets);
                    if combos_with_envs.is_empty() {
                        vals.push(Vec::new());
                        return Ok(());
                    }
                    let mut bodies: Vec<(Arc<Expr>, Env, i64)> = Vec::new();
                    for (combo, combo_env) in &combos_with_envs {
                        for (patterns, body) in &clauses {
                            if let Some((body_env, subst_cost)) =
                                crate::eval::forms::query::match_clause(
                                    patterns,
                                    combo,
                                    combo_env,
                                    funcs,
                                )
                            {
                                bodies.push((Arc::new(body.clone()), body_env, subst_cost));
                            }
                        }
                    }
                    if bodies.is_empty() {
                        vals.push(plain(Vec::new()));
                        return Ok(());
                    }
                    work.push(Task::Apply(Frame::Gather { n: bodies.len() }));
                    for (body, body_env, _) in bodies.into_iter().rev() {
                        work.push(Task::Apply(Frame::MergeEnv { env: body_env.clone() }));
                        work.push(Task::Eval {
                            expr: body,
                            env: body_env,
                        });
                    }
                    Ok(())
                }
            }
        }
    }
}
