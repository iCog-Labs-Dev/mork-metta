use crate::atom::Atom;
use crate::env::Env;
use crate::eval::shared::fresh;
use crate::eval::machine::budget::{ResultSet, plain};
use super::op::{Opcode, CaseBranch};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::parser::Expr;

#[derive(Clone)]
pub struct PendingCall {
    pub body_code: Arc<[Opcode]>,
    pub free_vars: Vec<String>,
    pub body_env: Env,
    pub locals_to_push: Vec<(Atom, Env)>,
    pub cost: i64,
}

/// ponytail: Loop and execution state for frame-based control flow.
pub enum CallFrameKind {
    Normal,
    Let {
        value_rs: Vec<(Atom, Env)>,
        next_idx: usize,
        pattern: Expr,
        pattern_vars: Vec<String>,
        free_vars_map: Vec<String>,
        body_code: Arc<[Opcode]>,
        results: ResultSet,
    },
    If {
        condition_rs: Vec<(Atom, Env)>,
        next_idx: usize,
        then_code: Arc<[Opcode]>,
        else_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
        had_nondet_truthy: bool,
        truthy_count: usize,
        results: ResultSet,
    },
    Case {
        scrutinee_rs: Vec<(Atom, Env)>,
        next_idx: usize,
        branches: Vec<CaseBranch>,
        results: ResultSet,
    },
    Call {
        name: String,
        arity: u8,
        pending_calls: Vec<PendingCall>,
        next_idx: usize,
        results: ResultSet,
    },
    Eval {
        target_rs: Vec<(Expr, Env)>,
        next_idx: usize,
        results: ResultSet,
    },
}

/// ponytail: Frame-based return state for flat control flow.
/// When Let/If execute their body inline (same VMState), a CallFrame
/// saves the parent's code, ip, env, and free-var context so we can
/// restore after the body completes. This avoids C-stack recursion
/// for structural nesting (let*/if chains inside function bodies).
pub struct CallFrame {
    pub return_ip: usize,
    pub return_code: Arc<[Opcode]>,
    pub locals_to_pop: usize,
    pub saved_base_env: Env,
    pub saved_locals: Vec<(Atom, Env)>,  // parent's locals for Call frames
    pub saved_free_vars_map: Vec<String>,
    pub saved_free_vars_bindings: Vec<Atom>,
    pub kind: CallFrameKind,
}

pub struct VMState {
    pub code: Arc<[Opcode]>,
    pub ip: usize,
    pub stack: Vec<ResultSet>,
    pub locals: Vec<(Atom, Env)>,
    pub free_vars_map: Vec<String>,     // Index to original free var name
    pub free_vars_bindings: Vec<Atom>,  // Index to instantiated fresh Atom
    pub frames: Vec<CallFrame>,
    pub budget: Option<i64>,
    pub cut_executed: bool,
}

impl VMState {
    pub fn new(code: Arc<[Opcode]>, free_vars_map: Vec<String>, budget: Option<i64>) -> Self {
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                let fresh_name = if fresh::is_generated_var_name(name) {
                    name.clone()
                } else {
                    let id = next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    format!("$__fresh_{hint}_{id}")
                };
                Atom::sym(&fresh_name)
            })
            .collect();

        VMState {
            code,
            ip: 0,
            stack: Vec::with_capacity(32),
            locals: Vec::with_capacity(16),
            free_vars_map,
            free_vars_bindings,
            frames: Vec::with_capacity(8),
            budget,
            cut_executed: false,
        }
    }

    pub fn new_with_parent(
        code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
        budget: Option<i64>,
        parent_map: &[String],
        parent_bindings: &[Atom],
    ) -> Self {
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                if let Some(pos) = parent_map.iter().position(|x| x == name) {
                    parent_bindings[pos].clone()
                } else if fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();

        VMState {
            code,
            ip: 0,
            stack: Vec::with_capacity(32),
            locals: Vec::with_capacity(16),
            free_vars_map,
            free_vars_bindings,
            frames: Vec::with_capacity(8),
            budget,
            cut_executed: false,
        }
    }
}

pub static FRESH_COUNTER: AtomicU64 = AtomicU64::new(100000);
pub fn next_fresh_id() -> u64 {
    FRESH_COUNTER.fetch_add(1, Ordering::Relaxed)
}
