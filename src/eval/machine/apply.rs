//! Continuation application logic.
//!
//! This module resumes suspended frames with child results and determines the
//! next machine actions required to continue evaluation.

use super::budget::{atoms_of, plain, ResultSet};
use super::frame::Frame;
use super::state::Transition;
use super::task::Task;
use crate::atom::Atom;
use crate::env::{Env, EnvNode};
use crate::func::FnTable;
use crate::parser::Expr;
use rayon::prelude::*;
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

    // ponytail: fast path for all-singleton option sets (no redundant vector clones)
    if options.iter().all(|o| o.len() == 1) {
        let mut combination = Vec::with_capacity(options.len());
        for option in options {
            combination.push(option[0].clone());
        }
        return vec![combination];
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


/// PeTTa semantics: variables are single-assignment — reject bindings that
/// would shadow a variable already present in the outer environment.
fn has_shadowing(new_env: &Env, outer_env: &Env) -> bool {
    if outer_env.is_empty_env() {
        return false;
    }
    match new_env.inner() {
        EnvNode::Empty => false,
        EnvNode::Cons { name, value: _, next } => {
            outer_env.get(name).is_some() || has_shadowing(next, outer_env)
        }
        EnvNode::Link { prefix, base } => {
            has_shadowing(prefix, outer_env) || has_shadowing(base, outer_env)
        }
    }
}

/// Lazy cartesian product: visits every combination via callback without
/// materialising the full M^K intermediate Vec. Uses O(depth) stack memory.
#[inline]
fn cartesian_product_apply<E>(
    options: &[Vec<Atom>],
    buf: &mut Vec<Atom>,
    f: &mut impl FnMut(&[Atom]) -> Result<(), E>,
) -> Result<(), E> {
    if options.is_empty() {
        return f(buf);
    }
    for atom in &options[0] {
        buf.push(atom.clone());
        cartesian_product_apply(&options[1..], buf, f)?;
        buf.pop();
    }
    Ok(())
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
    // ponytail: fast path for all-singleton result sets (bypasses redundant environment merging and prefix cloning)
    if sets.iter().all(|s| s.len() == 1) {
        let mut atoms = Vec::with_capacity(sets.len());
        let mut acc_env = Env::new();
        for rs in sets {
            let (atom, env) = &rs[0];
            atoms.push(atom.clone());
            acc_env = crate::eval::shared::pattern::prepend_env(env.clone(), &acc_env);
        }
        return vec![(atoms, acc_env)];
    }

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
                if out.len() > 1_000_000 {
                    return Err(
                        "result set exceeded 1 000 000 entries — possible infinite recursion \
                         (hint: replace `(range 0 inf)` loops with direct tail recursion)"
                            .into(),
                    );
                }
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
                _ if had_bindings => plain(vec![Atom::Expr(out.into())]),
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
                match crate::eval::shared::pattern::try_match_one(&pattern, value, &Env::new(), funcs)
                {
                    Ok(Some(matched)) => {
                        if has_shadowing(&matched, &env) {
                            eprintln!("warn: let pattern variable shadows outer binding — rejecting match");
                        } else {
                            let body_env = crate::eval::shared::env::prepend_chain(matched, &env);
                            branches.push((Arc::clone(&body), body_env));
                        }
                    }
                    Ok(None) => {
                        eprintln!(
                            "warn: let pattern {} does not match value {}",
                            pattern.to_string(),
                            value.to_sexpr_string(),
                        );
                    }
                    Err(e) => {
                        eprintln!("warn: let pattern match error: {}", e);
                    }
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
                Some(crate::atom::Atom::Expr(v)) => v.to_vec(),
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
            let call = crate::parser::Expr::List(Arc::from([func_expr, acc_expr, item_expr]));
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
        Frame::PythonImport { path, env } => {
            let space_rs = pop_n(vals, 1).pop().unwrap();
            let _space_ref = space_rs
                .into_iter()
                .next()
                .map(|(a, _)| a)
                .unwrap_or_else(|| crate::atom::Atom::sym("&self"));
            let import_dir = funcs.import_dir.lock().unwrap().clone();
            // Try as-is and with .py extension
            let py_path = std::path::Path::new(&path);
            let resolved = if py_path.exists() {
                Some(py_path.to_path_buf())
            } else {
                let with_ext = format!("{}.py", path);
                let py_ext = std::path::Path::new(&with_ext);
                if py_ext.exists() {
                    Some(py_ext.to_path_buf())
                } else {
                    // Search import dir
                    let in_dir = import_dir.join(&path);
                    if in_dir.exists() {
                        Some(in_dir)
                    } else {
                        let in_dir_ext = import_dir.join(&with_ext);
                        if in_dir_ext.exists() {
                            Some(in_dir_ext)
                        } else {
                            None
                        }
                    }
                }
            }
            .ok_or_else(|| {
                format!(
                    "import!: cannot find Python file '{}' (searched CWD and '{}')",
                    path,
                    import_dir.display()
                )
            })?;
            crate::eval::python::eval_py_import_library(&resolved)?;
            vals.push(super::budget::plain(vec![crate::atom::Atom::sym("true")]));
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
            let call = crate::parser::Expr::List(Arc::from([func_expr, acc_expr, item_expr]));
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
                match crate::eval::shared::pattern::try_match_one(pattern, value, &Env::new(), funcs)
                {
                    Ok(Some(matched)) => {
                        if has_shadowing(&matched, &env) {
                            eprintln!("warn: let* pattern variable shadows outer binding — rejecting match");
                            continue;
                        }
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
                    Ok(None) => {
                        eprintln!(
                            "warn: let* pattern {} does not match value {}",
                            pattern.to_string(),
                            value.to_sexpr_string(),
                        );
                    }
                    Err(e) => {
                        eprintln!("warn: let* pattern match error: {}", e);
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
            let n = branches.len();
            // Reverse so pop() gives original order (first branch evaluated first).
            let mut remaining: Vec<_> = branches.into_iter().rev().collect();
            let (first_expr, first_env) = remaining.pop().unwrap();
            work.push(Task::Apply(Frame::Gather { n }));
            if !remaining.is_empty() {
                work.push(Task::Apply(Frame::SpaceMatchStream { remaining }));
            }
            work.push(Task::Eval { expr: first_expr, env: first_env });
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
            vals.push(plain(vec![Atom::Expr(Arc::from(atoms_of(&result_set)))]));
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
                // Tail call: Gather{1} between MergeEnv and the deeper continuation
                // is a no-op (pop 1 ResultSet, re-emit unchanged). Remove it to save
                // one frame allocation per tail step — halves stack depth for linear
                // tail-recursive chain programs like iterative div/fib.
                let n = work.len();
                if n >= 2
                    && matches!(work[n - 1], Task::Apply(Frame::MergeEnv { .. }))
                    && matches!(work[n - 2], Task::Apply(Frame::Gather { n: 1 }))
                {
                    work.remove(n - 2);
                }
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
                Atom::Expr(elements) => vals.push(plain(elements.to_vec())),
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
            let mut lists = Vec::new();
            let mut buf = Vec::new();
            cartesian_product_apply(&tail_atoms, &mut buf, &mut |combo: &[Atom]| {
                let mut atoms = Vec::with_capacity(combo.len() + 1);
                atoms.push(head.clone());
                atoms.extend_from_slice(combo);
                lists.push(Atom::Expr(atoms.into()));
                Ok::<(), String>(())
            })?;
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
            let mut lists = Vec::new();
            let mut buf = Vec::new();
            cartesian_product_apply(&per_elem, &mut buf, &mut |combo: &[Atom]| {
                lists.push(Atom::Expr(Arc::from(combo)));
                Ok::<(), String>(())
            })?;
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
                                let mut results = Vec::new();
                                let mut buf = Vec::new();
                                cartesian_product_apply(&arg_options, &mut buf, &mut |slice: &[Atom]| {
                                    match func(slice, funcs) {
                                        Ok(nd) => { results.extend(nd); Ok(()) }
                                        Err(e) => Err(e),
                                    }
                                })?;
                                vals.push(plain(results));
                                return Ok(());
                            }
                        }
                        // Try user clauses
                        if let Some(clauses) =
                            crate::eval::forms::query::lookup_user_clauses(name, arity as u8, funcs)
                        {
                            let combos_with_envs = threaded_combinations(&arg_sets);
                            // Memo: single-combo pure calls only (multi-combo = ndet, skip).
                            let memo_key = if funcs.is_pure_fn(name, arity as u8)
                                && combos_with_envs.len() == 1
                            {
                                let k = (name.to_string(), combos_with_envs[0].0.clone());
                                if let Some(cached) = funcs.memo_get(&k) {
                                    vals.push(plain(cached));
                                    return Ok(());
                                }
                                Some(k)
                            } else {
                                None
                            };
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
                                let merged: Vec<Atom> = if bodies.len() > 1
                                    && funcs.is_parallelizable(name, arity as u8)
                                {
                                    bodies
                                        .into_par_iter()
                                        .map(|(body, body_env, _)| {
                                            super::step::run_rs(body, body_env, funcs, &mut None)
                                                .map(|rs| rs.into_iter().map(|(a, _)| a).collect::<Vec<_>>())
                                        })
                                        .collect::<Result<Vec<_>, _>>()?
                                        .into_iter()
                                        .flatten()
                                        .collect()
                                } else {
                                    let mut out = Vec::new();
                                    for (body, body_env, _) in bodies {
                                        let body_rs = super::step::run_rs(body, body_env, funcs, &mut None)?;
                                        out.extend(body_rs);
                                    }
                                    out.into_iter().map(|(a, _)| a).collect()
                                };
                                if let Some(key) = memo_key {
                                    funcs.memo_set(key, merged.clone());
                                }
                                vals.push(plain(merged));
                                return Ok(());
                            }
                        }
                        // Partial application: function exists at higher arity
                        if funcs.has_higher_arity(name, arity) {
                            let partial_args: Vec<Atom> = arg_options.into_iter().flatten().collect();
                            vals.push(plain(vec![
                                Atom::Expr(Arc::from([
                                    Atom::sym("partial"),
                                    Atom::Sym(name.clone()),
                                    Atom::Expr(Arc::from(partial_args)),
                                ]))
                            ]));
                            return Ok(());
                        }
                        // Fall through to data list
                    }
                    Atom::Expr(items) => {
                        // Check if this is a (partial fn-name (old-args...)) application
                        if items.len() == 3
                            && items[0] == Atom::sym("partial")
                        {
                            if let Atom::Sym(fn_name) = &items[1] {
                                if let Atom::Expr(old_args) = &items[2] {
                                    let arg_options: Vec<Vec<Atom>> = arg_sets.iter().map(atoms_of).collect();
                                    if arg_options.iter().any(|values| values.is_empty()) {
                                        vals.push(Vec::new());
                                        return Ok(());
                                    }
                                    let mut results = Vec::new();
                                    let mut buf = Vec::new();
                                    cartesian_product_apply(&arg_options, &mut buf, &mut |combo: &[Atom]| {
                                        let mut all_args: Vec<Atom> = old_args.to_vec();
                                        all_args.extend_from_slice(combo);
                                        let fn_expr = crate::parser::atom_to_expr(&Atom::Sym(fn_name.clone()))
                                            .unwrap_or(Expr::Symbol(fn_name.to_string()));
                                        let mut call_items = vec![fn_expr];
                                        for arg in &all_args {
                                            call_items.push(
                                                crate::parser::atom_to_expr(arg)
                                                    .unwrap_or(Expr::Symbol(arg.to_sexpr_string()))
                                            );
                                        }
                                        let call_expr = Expr::List(call_items.into());
                                        let body_rs = super::step::run_rs(
                                            Arc::new(call_expr),
                                            Env::new(),
                                            funcs,
                                            &mut None,
                                        )?;
                                        results.extend(body_rs.into_iter().map(|(a, _)| a));
                                        Ok::<(), String>(())
                                    })?;
                                    vals.push(plain(results));
                                    return Ok(());
                                }
                            }
                        }
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
            let mut lists = Vec::new();
            let mut buf = Vec::new();
            cartesian_product_apply(&all_atoms, &mut buf, &mut |combo: &[Atom]| {
                lists.push(Atom::Expr(Arc::from(combo)));
                Ok::<(), String>(())
            })?;
            vals.push(plain(lists));
            Ok(())
        }
        Frame::SpaceMatchStream { mut remaining } => {
            // One branch just completed (its result is on vals).
            // Fire the next branch, or do nothing if we're the last (Gather collects).
            if let Some((expr, env)) = remaining.pop() {
                work.push(Task::Apply(Frame::SpaceMatchStream { remaining }));
                work.push(Task::Eval { expr, env });
            }
            Ok(())
        }

        Frame::MemoStore { key } => {
            // Gather already pushed its result onto vals. Peek at it, store in
            // cache tagged with the current mutation stamp, leave it in place.
            if let Some(top) = vals.last() {
                let result: Vec<Atom> = top.iter().map(|(a, _)| a.clone()).collect();
                funcs.memo_set(key.clone(), result);
            }
            Ok(())
        }

        Frame::Progn { n } => {
            let mut sets = pop_n(vals, n);
            // Last arg evaluated last → its result is on top (end of sets)
            vals.push(sets.pop().unwrap_or_default());
            Ok(())
        }
        Frame::Prog1 { n } => {
            let mut sets = pop_n(vals, n);
            // First arg evaluated first → its result is at front
            vals.push(sets.into_iter().next().unwrap_or_default());
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
                    let mut results = Vec::new();
                    let mut last_err = None;
                    let mut buf = Vec::new();
                    cartesian_product_apply(&arg_options, &mut buf, &mut |slice: &[Atom]| {
                        match f(slice, funcs) {
                            Ok(nd) => { results.extend(nd); Ok::<(), String>(()) }
                            Err(err) => { last_err = Some(err); Ok(()) }
                        }
                    })?;
                    if results.is_empty() {
                        if let Some(err) = last_err {
                            return Err(err);
                        }
                    }
                    vals.push(plain(results));
                    Ok(())
                }
                super::task::Head::User {
                    name,
                    clauses,
                    lazy_mask: _,
                } => {
                    let combos_with_envs = threaded_combinations(&arg_sets);
                    if combos_with_envs.is_empty() {
                        vals.push(Vec::new());
                        return Ok(());
                    }
                    // Memo check: pure + single-combo only.
                    let memo_key = if funcs.is_pure_fn(&name, arity as u8)
                        && combos_with_envs.len() == 1
                    {
                        let k = (name.to_string(), combos_with_envs[0].0.clone());
                        if let Some(cached) = funcs.memo_get(&k) {
                            vals.push(plain(cached));
                            return Ok(());
                        }
                        Some(k)
                    } else {
                        None
                    };
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
                    // Parallel path: pure/SpaceRead functions with multiple matched bodies.
                    if bodies.len() > 1 && funcs.is_parallelizable(&name, arity as u8) {
                        let merged: Vec<(Atom, Env)> = bodies
                            .into_par_iter()
                            .map(|(body, body_env, _)| {
                                let be = body_env;
                                super::step::run_rs(body, be.clone(), funcs, &mut None)
                                    .map(|rs| {
                                        rs.into_iter().map(move |(a, result_env)| {
                                            let merged = crate::eval::shared::pattern::prepend_env(
                                                be.clone(), &result_env);
                                            (a, merged)
                                        }).collect::<Vec<_>>()
                                    })
                            })
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .flatten()
                            .collect();
                        if let Some(key) = memo_key {
                            let atoms_only: Vec<Atom> = merged.iter().map(|(a, _)| a.clone()).collect();
                            funcs.memo_set(key, atoms_only);
                        }
                        vals.push(merged);
                        return Ok(());
                    }
                    // Sequential path: impure or single-body.
                    if let Some(key) = memo_key {
                        work.push(Task::Apply(Frame::MemoStore { key }));
                    }
                    work.push(Task::Apply(Frame::Gather { n: bodies.len() }));
                    for (body, body_env, subst_cost) in bodies.into_iter().rev() {
                        work.push(Task::Apply(Frame::MergeEnv { env: body_env.clone() }));
                        work.push(Task::Eval {
                            expr: body.clone(),
                            env: body_env,
                        });
                        // debit query and substitution cost prior to body evaluation
                        let body_atom = crate::parser::expr_to_atom(&body);
                        let body_cost = crate::eval::machine::budget::calculate_cost(&body_atom).unwrap_or(0);
                        work.push(Task::Transition(Transition::Query {
                            cost: subst_cost + body_cost,
                        }));
                    }
                    Ok(())
                }
            }
        }
    }
}
