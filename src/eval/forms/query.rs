//! Helpers for query-style evaluation.
//!
//! This module contains the logic used for user-function application,
//! including clause lookup, substitution, lazy argument handling, and
//! query-related cost behavior.

use crate::atom::Atom;
use crate::env::Env;
use crate::func::Clause;
use crate::func::FnTable;
use crate::parser::Expr;

pub(crate) use super::super::shared::closure::{
    delayed_user_call_arg, eval_user_call_arg, eval_user_call_arg_slot, lazy_user_arg_mask,
};
pub(crate) use super::super::shared::subst::{subst_and_atomize, subst_expr_vars};

/// Prepare a single evaluated or delayed argument slot for query-style
/// function application.
pub(crate) fn prepare_arg_slot(
    expr: &Expr,
    env: &Env,
    funcs: &FnTable,
    lazy: bool,
) -> Result<Vec<Atom>, String> {
    eval_user_call_arg_slot(expr, env, funcs, lazy)
}

/// Compute the total structural cost of the bindings in an environment.
pub(crate) fn env_binding_cost(env: &Env) -> i64 {
    match env.inner() {
        crate::env::EnvNode::Empty => 0,
        crate::env::EnvNode::Cons { value, next, .. } => {
            crate::eval::machine::budget::calculate_cost(value).unwrap_or(0)
                + env_binding_cost(next)
        }
        crate::env::EnvNode::Link { prefix, base } => {
            env_binding_cost(prefix) + env_binding_cost(base)
        }
    }
}

/// Match one clause against one argument combination.
///
/// On success, this returns the environment produced by the match together
/// with the structural cost of the produced substitution.
pub(crate) fn match_clause(
    patterns: &[Expr],
    args: &[Atom],
    base_env: &Env,
    funcs: &FnTable,
) -> Option<(Env, i64)> {
    if patterns.len() != args.len() {
        return None;
    }

    let args_str: Vec<String> = args.iter().map(|a| a.to_sexpr_string()).collect();
    let pats_str: Vec<String> = patterns.iter().map(|p| format!("{:?}", p)).collect();

    let mut unification_env = Env::new();
    for (i, (pattern, arg)) in patterns.iter().zip(args.iter()).enumerate() {
        match crate::eval::shared::pattern::try_match_one(pattern, arg, &unification_env, funcs) {
            Ok(Some(new_env)) => unification_env = new_env,
            Ok(None) => {
                return None;
            }
            Err(e) => {
                return None;
            }
        }
    }

    let subst_cost = env_binding_cost(&unification_env);
    Some((
        crate::eval::shared::pattern::prepend_env(unification_env, base_env),
        subst_cost,
    ))
}

/// Collect lazy-mask-ready clause references for a user-defined function body.
pub(crate) fn collect_clause_refs<'a>(
    clauses: &'a [(Vec<Expr>, Expr)],
) -> Vec<(&'a [Expr], &'a Expr)> {
    clauses
        .iter()
        .map(|(patterns, body)| (patterns.as_slice(), body))
        .collect()
}

/// Look up cached user-function clauses by name and arity.
pub(crate) fn lookup_user_clauses(
    name: &str,
    arity: u8,
    funcs: &FnTable,
) -> Option<Vec<(Vec<Expr>, Expr)>> {
    let cache = funcs.fn_cache.read().unwrap();
    let clauses: &Vec<Clause> = cache.get(name)?.get(&arity)?;
    Some(
        clauses
            .iter()
            .map(|clause| (clause.patterns.clone(), clause.body.clone()))
            .collect(),
    )
}
