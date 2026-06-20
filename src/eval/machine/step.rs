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
    let mut work = Vec::with_capacity(64);
    work.push(super::task::Task::Eval { expr: root, env: root_env });
    let mut vals: Vec<ResultSet> = Vec::with_capacity(32);

    while let Some(task) = work.pop() {
        if work.len() + vals.len() > 2_000_000 {
            return Err(format!(
                "evaluation stack overflow: {} pending tasks, {} result sets — \
                 possible infinite recursion (hint: use direct tail recursion \
                 instead of `(range 0 inf)` style loops)",
                work.len(),
                vals.len()
            ));
        }
        match task {
            super::task::Task::Eval { expr, env } => {
                super::dispatch::dispatch_expr(&expr, &env, funcs, &mut work, &mut vals)?;
            }
            super::task::Task::Apply(frame) => {
                super::apply::apply_frame(frame, funcs, &mut work, &mut vals)?;
            }
            super::task::Task::Transition(transition) => {
                let result_set = super::transition::apply_transition(transition, funcs, budget)?;
                vals.push(result_set);
            }
        }
    }

    Ok(vals.pop().unwrap_or_default())
}
