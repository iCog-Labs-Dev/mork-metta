use crate::atom::Atom;
use crate::env::Env;
use crate::eval::shared::fresh;
use crate::eval::machine::budget::{ResultSet, plain};
use super::op::Opcode;
use std::sync::atomic::{AtomicU64, Ordering};

pub struct CallFrame {
    pub return_ip: usize,
    pub locals_start: usize,
    pub locals_count: usize,
}

pub struct VMState {
    pub code: Vec<Opcode>,
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
    pub fn new(code: Vec<Opcode>, free_vars_map: Vec<String>, budget: Option<i64>) -> Self {
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
        code: Vec<Opcode>,
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

static FRESH_COUNTER: AtomicU64 = AtomicU64::new(100000);
fn next_fresh_id() -> u64 {
    FRESH_COUNTER.fetch_add(1, Ordering::Relaxed)
}
