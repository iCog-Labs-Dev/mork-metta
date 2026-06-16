//! Public entrypoints for expression evaluation.
//!
//! This module defines the functions that evaluate expressions and return
//! result streams. It provides the external interface to the evaluator without
//! exposing machine internals.

use super::machine::step;
use crate::env::Env;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

/// Evaluate an expression and return its result stream.
pub fn eval_scope(expr: &Expr, env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    step::run_as_ndet(expr, env, funcs)
}

/// Evaluate an expression with an optional reduction budget.
pub fn eval_with_state(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    cost_budget: Option<i64>,
) -> Result<(NDet, Option<i64>), String> {
    let mut budget = cost_budget;
    let results = step::run_budgeted(expr, env, funcs, &mut budget)?;
    Ok((NDet::stream(results.into_iter()), budget))
}
