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

    // Try compiling with bytecode VM first
    let mut comp = super::vm::VMCompiler::new(&[], None);
    let mut code = Vec::new();
    if comp.compile(&root, &mut code, false).is_ok() {
        let state = super::vm::VMState::new(code, comp.free_vars, *budget);
        match super::vm::run_vm(state, funcs, &root_env) {
            Ok((rs, sub_budget)) => {
                *budget = sub_budget;
                return Ok(rs);
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    // reuse vectors from thread-local pools to prevent the allocation storm of nested run_rs calls
    thread_local! {
        static WORK_POOL: std::cell::RefCell<Vec<Vec<super::task::Task>>> = const { std::cell::RefCell::new(Vec::new()) };
        static VALS_POOL: std::cell::RefCell<Vec<Vec<super::budget::ResultSet>>> = const { std::cell::RefCell::new(Vec::new()) };
    }

    let mut work = WORK_POOL.with(|p| p.borrow_mut().pop()).unwrap_or_else(|| Vec::with_capacity(64));
    let mut vals = VALS_POOL.with(|p| p.borrow_mut().pop()).unwrap_or_else(|| Vec::with_capacity(32));
    work.clear();
    vals.clear();

    work.push(super::task::Task::Eval { expr: root, env: root_env });
    let res = run_rs_loop(&mut work, &mut vals, funcs, budget);

    work.clear();
    vals.clear();
    WORK_POOL.with(|p| p.borrow_mut().push(work));
    VALS_POOL.with(|p| p.borrow_mut().push(vals));

    res
}

fn run_rs_loop(
    work: &mut Vec<super::task::Task>,
    vals: &mut Vec<super::budget::ResultSet>,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<ResultSet, String> {
    // Debug: set MORK_DEBUG_STACK=1 to log a work-stack histogram as it grows.
    static DEBUG_STACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let debug_stack = *DEBUG_STACK.get_or_init(|| std::env::var_os("MORK_DEBUG_STACK").is_some());
    let mut next_log = 250_000usize;

    while let Some(task) = work.pop() {
        if debug_stack && work.len() >= next_log {
            eprintln!("[stack] work={} vals={} | {}", work.len(), vals.len(), stack_histogram(work));
            next_log += 250_000;
        }
        if work.len() + vals.len() > 2_000_000 {
            if debug_stack {
                eprintln!("[stack] OVERFLOW histogram: {}", stack_histogram(work));
            }
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
                let _profile = crate::profile::ProfileGuard::new("run_rs::Eval");
                super::dispatch::dispatch_expr(&expr, &env, funcs, work, vals)?;
            }
            super::task::Task::Apply(frame) => {
                let name = match &frame {
                    super::frame::Frame::Call { .. } => "run_rs::Apply::Call",
                    super::frame::Frame::Gather { .. } => "run_rs::Apply::Gather",
                    super::frame::Frame::MergeEnv { .. } => "run_rs::Apply::MergeEnv",
                    super::frame::Frame::IfGather { .. } => "run_rs::Apply::IfGather",
                    super::frame::Frame::LetStarBind { .. } => "run_rs::Apply::LetStarBind",
                    super::frame::Frame::LetMatch { .. } => "run_rs::Apply::LetMatch",
                    super::frame::Frame::ChainBind { .. } => "run_rs::Apply::ChainBind",
                    super::frame::Frame::Progn { .. } => "run_rs::Apply::Progn",
                    super::frame::Frame::Prog1 { .. } => "run_rs::Apply::Prog1",
                    super::frame::Frame::Discard => "run_rs::Apply::Discard",
                    super::frame::Frame::Forward(_) => "run_rs::Apply::Forward",
                    super::frame::Frame::DataList { .. } | super::frame::Frame::DataListWithHead { .. } => "run_rs::Apply::DataList",
                    _ => "run_rs::Apply::Other",
                };
                let _profile = crate::profile::ProfileGuard::new(name);
                super::apply::apply_frame(frame, funcs, work, vals)?;
            }
            super::task::Task::Transition(transition) => {
                let _profile = crate::profile::ProfileGuard::new("run_rs::Transition");
                if let Some(result_set) =
                    super::transition::apply_transition(transition, funcs, budget)?
                {
                    vals.push(result_set);
                }
            }
        }
    }

    Ok(vals.pop().unwrap_or_default())
}

/// Debug helper: tally the kinds of pending tasks on the work stack. Used to
/// diagnose unbounded growth (e.g. missing tail-call optimization).
fn stack_histogram(work: &[super::task::Task]) -> String {
    use super::frame::Frame;
    use super::task::Task;
    let mut counts: std::collections::BTreeMap<&'static str, usize> = std::collections::BTreeMap::new();
    for t in work {
        let key = match t {
            Task::Eval { .. } => "Eval",
            Task::Transition(_) => "Transition",
            Task::Apply(f) => match f {
                Frame::Call { .. } => "Call",
                Frame::Gather { .. } => "Gather",
                Frame::MergeEnv { .. } => "MergeEnv",
                Frame::IfGather { .. } => "IfGather",
                Frame::LetStarBind { .. } => "LetStarBind",
                Frame::LetMatch { .. } => "LetMatch",
                Frame::ChainBind { .. } => "ChainBind",
                Frame::Progn { .. } => "Progn",
                Frame::Prog1 { .. } => "Prog1",
                Frame::Discard => "Discard",
                Frame::Forward(_) => "Forward",
                Frame::DataList { .. } | Frame::DataListWithHead { .. } => "DataList",
                _ => "OtherFrame",
            },
        };
        *counts.entry(key).or_insert(0) += 1;
    }
    counts
        .iter()
        .map(|(k, v)| format!("{k}:{v}"))
        .collect::<Vec<_>>()
        .join(" ")
}
