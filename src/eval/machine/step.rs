//! Stepping logic for machine execution.
//!
//! This module advances the evaluator by repeatedly dispatching expressions,
//! applying continuation frames, and executing direct state transitions.

use super::budget::{atoms_of, ResultSet};
use crate::atom::Atom;
use crate::env::Env;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;
use std::sync::Arc;

/// Evaluate an expression to a nondeterministic result stream.
pub fn run_as_ndet(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let results = run(expr, env, funcs)?;
    Ok(NDet::stream(results.into_iter()))
}

/// Evaluate an expression to an eager ordered result multiset.
pub(crate) fn run(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    let mut budget = None;
    let results = run_rs(Arc::new(expr.clone()), env.clone(), funcs, &mut budget)?;
    Ok(atoms_of(&results))
}

/// Evaluate an expression with an optional reduction budget.
pub(crate) fn run_budgeted(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<Vec<Atom>, String> {
    let results = run_rs(Arc::new(expr.clone()), env.clone(), funcs, budget)?;
    Ok(atoms_of(&results))
}

/// Run the machine until it produces a final result set.
pub(crate) fn run_rs(
    root: Arc<Expr>,
    root_env: Env,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<ResultSet, String> {
    let _profile = crate::profile::ProfileGuard::new("run_rs");
    crate::env::clear_lookup_cache();

    // Compiling with bytecode VM
    let mut comp = super::vm::VMCompiler::new(&[], None);
    let mut code = Vec::new();
    comp.compile(&root, &mut code, false)?;
    let state = super::vm::VMState::new(std::sync::Arc::from(code), comp.free_vars.clone(), *budget);
    let mut sub_env = root_env.clone();
    for (i, name) in comp.free_vars.iter().enumerate() {
        if let Some(val) = root_env.get(name) {
            if let crate::atom::Atom::Sym(fresh_name) = &state.free_vars_bindings[i] {
                sub_env = sub_env.extend(fresh_name, val.clone());
            }
        }
    }
    let (rs, sub_budget, _) = super::vm::run_vm(state, funcs, &sub_env)?;
    *budget = sub_budget;
    Ok(rs)
}
