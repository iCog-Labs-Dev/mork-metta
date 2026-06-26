use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use crate::func::{FnTable, FunctionKind};
use crate::eval::machine::budget::{ResultSet, plain};
use super::op::{Opcode, VmExit, CaseBranch, QuoteVarSource, QuoteVarMatch};
use super::state::{VMState, CallFrame, CallFrameKind};
use std::sync::Arc;

use std::cell::Cell;
use std::cell::RefCell;
use std::collections::HashMap;

/// Cached compilation of a user-defined function clause body.
#[derive(Clone)]
struct CompiledClause {
    body_code: std::sync::Arc<[Opcode]>,
    free_vars: Vec<String>,
    locals: Vec<String>,
}

thread_local! {
    static FN_BYTECODE_CACHE: RefCell<HashMap<(String, u8), Vec<CompiledClause>>> = RefCell::new(HashMap::new());
    static VM_DEPTH: Cell<u32> = Cell::new(0);
}

fn intern_name(name: &str) -> &'static str {
    static INTERNER: std::sync::OnceLock<std::sync::Mutex<HashMap<String, &'static str>>> =
        std::sync::OnceLock::new();
    let map = INTERNER.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    let mut map = map.lock().unwrap();
    *map.entry(name.to_string()).or_insert_with(|| {
        Box::leak(name.to_string().into_boxed_str())
    })
}

fn replace_at_path(atom: &mut Atom, path: &[usize], val: Atom) {
    if path.is_empty() {
        *atom = val;
        return;
    }
    if let Atom::Expr(expr_data) = atom {
        let mut items = expr_data.to_vec();
        if path[0] < items.len() {
            replace_at_path(&mut items[path[0]], &path[1..], val);
            *atom = Atom::Expr(crate::atom::expr_data(items));
        }
    }
}


struct VmDepthGuard;
impl VmDepthGuard {
    fn enter() -> Self {
        VM_DEPTH.with(|d| {
            let prev = d.get();
            d.set(prev + 1);
            if prev == 0 {
                FN_BYTECODE_CACHE.with(|c| c.borrow_mut().clear());
            }
        });
        VmDepthGuard
    }
}
impl Drop for VmDepthGuard {
    fn drop(&mut self) {
        VM_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

pub fn run_vm(
    mut state: VMState,
    funcs: &FnTable,
    initial_base_env: &Env,
) -> Result<(ResultSet, Option<i64>, VmExit), String> {
    super::compiler::set_current_funcs(funcs);
    let mut base_env = initial_base_env.clone();
    let _guard = VmDepthGuard::enter();
    static DEBUG_VM: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);
    let debug_vm = match DEBUG_VM.load(std::sync::atomic::Ordering::Relaxed) {
        0 => {
            let val = std::env::var_os("MORK_DEBUG_VM").is_some();
            DEBUG_VM.store(if val { 2 } else { 1 }, std::sync::atomic::Ordering::Relaxed);
            val
        }
        1 => false,
        _ => true,
    };
    if debug_vm {
        eprintln!("--- VM CODE ---");
        for (i, op) in state.code.iter().enumerate() {
            eprintln!("{:03}: {:?}", i, op);
        }
        eprintln!("----------------");
    }

    loop {
        while state.ip < state.code.len() {
        let op = &state.code[state.ip];
            let _profile = if cfg!(feature = "profile") {
                let name = match state.frames.last() {
                    Some(frame) => match &frame.kind {
                        CallFrameKind::Call { name, .. } => *name,
                        _ => match op {
                            Opcode::Call(_) => "Opcode::Call",
                            Opcode::Const(_) => "Opcode::Const",
                            Opcode::ConstQuote { .. } => "Opcode::ConstQuote",
                            Opcode::Load(_) => "Opcode::Load",
                            Opcode::Store(_) => "Opcode::Store",
                            Opcode::LoadFree(_) => "Opcode::LoadFree",
                            Opcode::Pop => "Opcode::Pop",
                            Opcode::Jump(_) => "Opcode::Jump",
                            Opcode::JumpIfEmpty(_) => "Opcode::JumpIfEmpty",
                            Opcode::JumpIfFalsy(_) => "Opcode::JumpIfFalsy",
                            Opcode::PopLocals(_) => "Opcode::PopLocals",
                            Opcode::TailCallSelf => "Opcode::TailCallSelf",
                            Opcode::UnifyPattern(_, _) => "Opcode::UnifyPattern",
                            Opcode::AddAtom { .. } => "Opcode::AddAtom",
                            Opcode::RemAtom { .. } => "Opcode::RemAtom",
                            Opcode::DebitBudget(_) => "Opcode::DebitBudget",
                            Opcode::Collapse => "Opcode::Collapse",
                            Opcode::Superpose(_) => "Opcode::Superpose",
                            Opcode::SuperposeUnpack => "Opcode::SuperposeUnpack",
                            Opcode::Eval => "Opcode::Eval",
                            Opcode::Lambda { .. } => "Opcode::Lambda",
                            Opcode::Unify { .. } => "Opcode::Unify",
                            Opcode::ConstEmpty => "Opcode::ConstEmpty",
                            Opcode::Cut => "Opcode::Cut",
                            Opcode::Println => "Opcode::Println",
                            Opcode::Readln => "Opcode::Readln",
                            Opcode::Let { .. } => "Opcode::Let",
                            Opcode::If { .. } => "Opcode::If",
                            Opcode::Case { .. } => "Opcode::Case",
                            Opcode::Match { .. } => "Opcode::Match",
                            Opcode::Test => "Opcode::Test",
                            Opcode::Foldall => "Opcode::Foldall",
                            Opcode::Forall => "Opcode::Forall",
                            Opcode::Foldl => "Opcode::Foldl",
                            Opcode::FoldlLambda { .. } => "Opcode::FoldlLambda",
                            Opcode::MapAtomLambda { .. } => "Opcode::MapAtomLambda",
                            Opcode::FilterAtomLambda { .. } => "Opcode::FilterAtomLambda",
                            Opcode::Once { .. } => "Opcode::Once",
                            Opcode::Progn { .. } => "Opcode::Progn",
                            Opcode::Prog1 { .. } => "Opcode::Prog1",
                            Opcode::Chain { .. } => "Opcode::Chain",
                            Opcode::Within { .. } => "Opcode::Within",
                            Opcode::WithMutex { .. } => "Opcode::WithMutex",
                            Opcode::Transaction { .. } => "Opcode::Transaction",
                            Opcode::ImportFile { .. } => "Opcode::ImportFile",
                            Opcode::PythonImport { .. } => "Opcode::PythonImport",
                            Opcode::PyCall { .. } => "Opcode::PyCall",
                            Opcode::PyEval { .. } => "Opcode::PyEval",
                            Opcode::ImportDynamic => "Opcode::ImportDynamic",
                            Opcode::MapAtomPatternLambda { .. } => "Opcode::MapAtomPatternLambda",
                            Opcode::FilterAtomPatternLambda { .. } => "Opcode::FilterAtomPatternLambda",
                        }
                    },
                    None => match op {
                        Opcode::Call(_) => "Opcode::Call",
                        Opcode::Const(_) => "Opcode::Const",
                        Opcode::ConstQuote { .. } => "Opcode::ConstQuote",
                        Opcode::Load(_) => "Opcode::Load",
                        Opcode::Store(_) => "Opcode::Store",
                        Opcode::LoadFree(_) => "Opcode::LoadFree",
                        Opcode::Pop => "Opcode::Pop",
                        Opcode::Jump(_) => "Opcode::Jump",
                        Opcode::JumpIfEmpty(_) => "Opcode::JumpIfEmpty",
                        Opcode::JumpIfFalsy(_) => "Opcode::JumpIfFalsy",
                        Opcode::PopLocals(_) => "Opcode::PopLocals",
                        Opcode::TailCallSelf => "Opcode::TailCallSelf",
                        Opcode::UnifyPattern(_, _) => "Opcode::UnifyPattern",
                        Opcode::AddAtom { .. } => "Opcode::AddAtom",
                        Opcode::RemAtom { .. } => "Opcode::RemAtom",
                        Opcode::DebitBudget(_) => "Opcode::DebitBudget",
                        Opcode::Collapse => "Opcode::Collapse",
                        Opcode::Superpose(_) => "Opcode::Superpose",
                        Opcode::SuperposeUnpack => "Opcode::SuperposeUnpack",
                        Opcode::Eval => "Opcode::Eval",
                        Opcode::Lambda { .. } => "Opcode::Lambda",
                        Opcode::Unify { .. } => "Opcode::Unify",
                        Opcode::ConstEmpty => "Opcode::ConstEmpty",
                        Opcode::Cut => "Opcode::Cut",
                        Opcode::Println => "Opcode::Println",
                        Opcode::Readln => "Opcode::Readln",
                        Opcode::Let { .. } => "Opcode::Let",
                        Opcode::If { .. } => "Opcode::If",
                        Opcode::Case { .. } => "Opcode::Case",
                        Opcode::Test => "Opcode::Test",
                        Opcode::Match { .. } => "Opcode::Match",
                        Opcode::Foldall => "Opcode::Foldall",
                        Opcode::Forall => "Opcode::Forall",
                        Opcode::Foldl => "Opcode::Foldl",
                        Opcode::FoldlLambda { .. } => "Opcode::FoldlLambda",
                        Opcode::MapAtomLambda { .. } => "Opcode::MapAtomLambda",
                        Opcode::FilterAtomLambda { .. } => "Opcode::FilterAtomLambda",
                        Opcode::Once { .. } => "Opcode::Once",
                        Opcode::Progn { .. } => "Opcode::Progn",
                        Opcode::Prog1 { .. } => "Opcode::Prog1",
                        Opcode::Chain { .. } => "Opcode::Chain",
                        Opcode::Within { .. } => "Opcode::Within",
                        Opcode::WithMutex { .. } => "Opcode::WithMutex",
                        Opcode::Transaction { .. } => "Opcode::Transaction",
                        Opcode::ImportFile { .. } => "Opcode::ImportFile",
                        Opcode::PythonImport { .. } => "Opcode::PythonImport",
                        Opcode::PyCall { .. } => "Opcode::PyCall",
                        Opcode::PyEval { .. } => "Opcode::PyEval",
                        Opcode::ImportDynamic => "Opcode::ImportDynamic",
                        Opcode::MapAtomPatternLambda { .. } => "Opcode::MapAtomPatternLambda",
                        Opcode::FilterAtomPatternLambda { .. } => "Opcode::FilterAtomPatternLambda",
                    }
                };
                Some(crate::profile::ProfileGuard::new(name))
            } else {
                None
            };
        if debug_vm {
            eprintln!("IP: {:03} | OP: {:?} | STACK: {:?} | LOCALS: {:?}", state.ip, op, state.stack, state.locals);
        }
        match op {
            Opcode::Const(atom) => {
                state.stack.push(plain(vec![atom.clone()]));
                state.ip += 1;
            }
            Opcode::ConstQuote { template, vars } => {
                let mut result = template.clone();
                for var in vars {
                    let val = match var.source {
                        QuoteVarSource::Local(pos) => {
                            if (pos as usize) < state.locals.len() {
                                state.locals[pos as usize].0.clone()
                            } else {
                                Atom::sym("()")
                            }
                        }
                        QuoteVarSource::Free(pos) => {
                            if (pos as usize) < state.free_vars_bindings.len() {
                                state.free_vars_bindings[pos as usize].clone()
                            } else {
                                Atom::sym("()")
                            }
                        }
                    };
                    replace_at_path(&mut result, &var.path, val);
                }
                state.stack.push(plain(vec![result]));
                state.ip += 1;
            }
            Opcode::Load(idx) => {
                let (val, env) = state.locals[*idx as usize].clone();
                let resolved = match &val {
                    Atom::Sym(s) if s.starts_with('$') => {
                        crate::eval::shared::env::lookup(&env, s)
                            .or_else(|| crate::eval::shared::env::lookup(&base_env, s))
                            .unwrap_or(val)
                    }
                    _ => val,
                };
                state.stack.push(vec![(resolved, env)]);
                state.ip += 1;
            }
            Opcode::Store(idx) => {
                let mut rs = state.stack.pop().ok_or("VM stack underflow on Store")?;
                if let Some((atom, env)) = rs.pop() {
                    if state.locals.len() <= *idx as usize {
                        state.locals.resize(*idx as usize + 1, (Atom::sym("()"), Env::new()));
                    }
                    state.locals[*idx as usize] = (atom, env);
                } else {
                    return Err("Cannot store empty value".into());
                }
                state.ip += 1;
            }
            Opcode::LoadFree(idx) => {
                let fresh = state.free_vars_bindings[*idx as usize].clone();
                let resolved = match &fresh {
                    Atom::Sym(s) if s.starts_with('$') => {
                        crate::eval::shared::env::lookup(&base_env, s).unwrap_or(fresh)
                    }
                    _ => fresh,
                };
                state.stack.push(vec![(resolved, base_env.clone())]);
                state.ip += 1;
            }
            Opcode::Pop => {
                state.stack.pop().ok_or("VM stack underflow on Pop")?;
                state.ip += 1;
            }
            Opcode::Jump(target) => {
                state.ip = *target;
            }
            Opcode::JumpIfEmpty(target) => {
                let top = state.stack.pop().ok_or("VM stack underflow on JumpIfEmpty")?;
                if top.is_empty() {
                    state.stack.push(Vec::new());
                    state.ip = *target;
                } else {
                    state.ip += 1;
                }
            }
            Opcode::JumpIfFalsy(target) => {
                let top = state.stack.pop().ok_or("VM stack underflow on JumpIfFalsy")?;
                let is_falsy = if top.is_empty() {
                    true
                } else if let Some((atom, _)) = top.first() {
                    !atom.is_truthy()
                } else {
                    false
                };
                if is_falsy {
                    state.ip = *target;
                } else {
                    state.ip += 1;
                }
            }
            Opcode::PopLocals(count) => {
                let new_len = state.locals.len().saturating_sub(*count as usize);
                state.locals.truncate(new_len);
                state.ip += 1;
            }
            Opcode::UnifyPattern(pattern, start_idx) => {
                let val_rs = state.stack.pop().ok_or("VM stack underflow on UnifyPattern")?;
                if val_rs.is_empty() {
                    state.stack.push(Vec::new());
                    state.ip += 1;
                    continue;
                }
                let mut matched_any = false;
                if let Some((value, _env)) = val_rs.first() {
                    if let Ok(Some(matched_env)) = crate::eval::shared::pattern::try_match_one(
                        pattern,
                        value,
                        &Env::new(),
                        funcs,
                    ) {
                        let mut pattern_vars = Vec::new();
                        collect_pattern_vars(pattern, &mut pattern_vars);
                        for (i, var) in pattern_vars.iter().enumerate() {
                            let bound_val = matched_env.get(var).unwrap_or(Atom::sym("()"));
                            let idx = *start_idx as usize + i;
                            if state.locals.len() <= idx {
                                state.locals.resize(idx + 1, (Atom::sym("()"), Env::new()));
                            }
                            state.locals[idx] = (bound_val, Env::new());
                        }
                        matched_any = true;
                    }
                }
                if matched_any {
                    state.stack.push(val_rs);
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::AddAtom { expr, local_names } => {
                let space_rs = state.stack.pop().ok_or("VM stack underflow on AddAtom space")?;
                
                let mut current_env = base_env.clone();
                for (i, name) in local_names.iter().enumerate() {
                    if let Some((val, _val_env)) = state.locals.get(i) {
                        current_env = crate::eval::shared::env::prepend_chain(
                            crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                            &current_env,
                        );
                    }
                }
                
                let atom = crate::eval::shared::subst::subst_and_atomize(expr, &current_env);
                let cost = crate::eval::machine::budget::calculate_cost(&atom).unwrap_or(0);
                if let Some(b) = state.budget {
                    if b <= cost {
                        return Err("Budget exhausted".into());
                    }
                    state.budget = Some(b - cost);
                }
                if let Some((space_ref, _)) = space_rs.first() {
                    crate::space::mutate::add_atom(funcs, space_ref, &atom)?;
                    state.stack.push(plain(vec![Atom::sym("true")]));
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::RemAtom { expr, local_names } => {
                let space_rs = state.stack.pop().ok_or("VM stack underflow on RemAtom space")?;
                
                let mut current_env = base_env.clone();
                for (i, name) in local_names.iter().enumerate() {
                    if let Some((val, _val_env)) = state.locals.get(i) {
                        current_env = crate::eval::shared::env::prepend_chain(
                            crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                            &current_env,
                        );
                    }
                }
                
                let atom = crate::eval::shared::subst::subst_and_atomize(expr, &current_env);
                let cost = crate::eval::machine::budget::calculate_cost(&atom).unwrap_or(0);
                if let Some(b) = state.budget {
                    if b <= cost {
                        return Err("Budget exhausted".into());
                    }
                    state.budget = Some(b - cost);
                }
                if let Some((space_ref, _)) = space_rs.first() {
                    let removed = crate::space::mutate::remove_atom(funcs, space_ref, &atom)?;
                    state.stack.push(plain(vec![if removed {
                        Atom::sym("true")
                    } else {
                        Atom::sym("")
                    }]));
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::Lambda { params, body, local_names } => {
                let mut current_env = base_env.clone();
                for (i, name) in local_names.iter().enumerate() {
                    if let Some((val, _val_env)) = state.locals.get(i) {
                        current_env = crate::eval::shared::env::prepend_chain(
                            crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                            &current_env,
                        );
                    }
                }
                state.stack.push(plain(vec![Atom::Closure(Box::new(
                    crate::atom::ClosureData {
                        params: params.clone(),
                        body: body.clone(),
                        env: current_env,
                    }
                ))]));
                state.ip += 1;
            }
            Opcode::Unify {
                pattern_a,
                pattern_b,
                then_code,
                else_code,
                pattern_vars,
                local_names,
                free_vars_map,
            } => {
                let val_b_rs = state.stack.pop().ok_or("VM stack underflow on Unify B")?;
                let val_a_rs = state.stack.pop().ok_or("VM stack underflow on Unify A")?;

                let mut current_env = base_env.clone();
                for (i, name) in local_names.iter().enumerate() {
                    if let Some((val, _val_env)) = state.locals.get(i) {
                        current_env = crate::eval::shared::env::prepend_chain(
                            crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                            &current_env,
                        );
                    }
                }

                let first_a = val_a_rs.first().map(|(a, _)| a);
                let is_space = match first_a {
                    Some(Atom::Sym(s)) => s.starts_with('&'),
                    _ => false,
                };

                let mut matched_any = false;
                let mut results = Vec::new();

                if is_space {
                    let space_ref = first_a.unwrap();
                    let matches = crate::space::query::collect_match_results(
                        funcs, space_ref, pattern_b, &current_env,
                    )?;
                    // Precompute bindings once for the entire Unify block
                    let precomputed_bindings: Vec<Atom> = free_vars_map
                        .iter()
                        .map(|name| {
                            if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                                state.free_vars_bindings[pos].clone()
                            } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                                Atom::sym(name)
                            } else {
                                let id = crate::eval::machine::vm::state::next_fresh_id();
                                let hint = name.strip_prefix('$').unwrap_or(name);
                                let fresh_name = format!("$__fresh_{hint}_{id}");
                                Atom::sym(&fresh_name)
                            }
                        })
                        .collect();

                    if matches.is_empty() {
                        let mut sub_state_locals = Vec::with_capacity(state.locals.len());
                        for val in &state.locals {
                            sub_state_locals.push(val.clone());
                        }
                        let sub_state = VMState {
                            code: else_code.clone(),
                            ip: 0,
                            stack: Vec::new(),
                            locals: sub_state_locals,
                            free_vars_map: free_vars_map.clone(),
                            free_vars_bindings: precomputed_bindings.clone(),
                            frames: Vec::new(),
                            budget: state.budget,
                            cut_executed: false,
                        };
                        let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &current_env)?;
                        state.budget = sub_budget;
                        results.extend(res);
                        match exit_status {
                            VmExit::Cut => { state.cut_executed = true; }
                            VmExit::TailCall(new_locals) => {
                                return Ok((results, state.budget, VmExit::TailCall(new_locals)));
                            }
                            VmExit::Normal => {}
                        }
                    } else {
                        matched_any = true;
                        for m in matches {
                            let mut sub_state_locals = Vec::with_capacity(state.locals.len() + pattern_vars.len());
                            for val in &state.locals {
                                sub_state_locals.push(val.clone());
                            }
                            for var in pattern_vars {
                                let bound = m.bindings.iter()
                                    .find(|(k, _)| k.as_ref() == var.as_str())
                                    .map(|(_, v)| (**v).clone())
                                    .unwrap_or_else(|| Atom::sym("()"));
                                sub_state_locals.push((bound, Env::new()));
                            }
                            let sub_state = VMState {
                                code: then_code.clone(),
                                ip: 0,
                                stack: Vec::new(),
                                locals: sub_state_locals,
                                free_vars_map: free_vars_map.clone(),
                                free_vars_bindings: precomputed_bindings.clone(),
                                frames: Vec::new(),
                                budget: state.budget,
                                cut_executed: false,
                            };
                            let sub_env = crate::eval::shared::env::bind_all(&current_env, &m.bindings);
                            let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &sub_env)?;
                            state.budget = sub_budget;
                            results.extend(res);
                            match exit_status {
                                VmExit::Cut => {
                                    state.cut_executed = true;
                                    break;
                                }
                                VmExit::TailCall(new_locals) => {
                                    return Ok((results, state.budget, VmExit::TailCall(new_locals)));
                                }
                                VmExit::Normal => {}
                            }
                        }
                    }
                } else {
                    // Precompute bindings once for the else branch's loop
                    let precomputed_bindings: Vec<Atom> = free_vars_map
                        .iter()
                        .map(|name| {
                            if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                                state.free_vars_bindings[pos].clone()
                            } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                                Atom::sym(name)
                            } else {
                                let id = crate::eval::machine::vm::state::next_fresh_id();
                                let hint = name.strip_prefix('$').unwrap_or(name);
                                let fresh_name = format!("$__fresh_{hint}_{id}");
                                Atom::sym(&fresh_name)
                            }
                        })
                        .collect();

                    for (val_b, env_b) in val_b_rs {
                        if let Some((val_a, env_a)) = val_a_rs.first() {
                            let match_env = crate::eval::shared::pattern::prepend_env(env_b, &current_env);
                            match crate::eval::shared::pattern::try_match_one(pattern_a, &val_b, &match_env, funcs)? {
                                Some(matched_env) => {
                                    matched_any = true;
                                    let mut sub_state_locals = Vec::with_capacity(state.locals.len() + pattern_vars.len());
                                    for val in &state.locals {
                                        sub_state_locals.push(val.clone());
                                    }
                                    for var in pattern_vars {
                                        let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                                        sub_state_locals.push((bound, Env::new()));
                                    }
                                    let sub_state = VMState {
                                        code: then_code.clone(),
                                        ip: 0,
                                        stack: Vec::new(),
                                        locals: sub_state_locals,
                                        free_vars_map: free_vars_map.clone(),
                                        free_vars_bindings: precomputed_bindings.clone(),
                                        frames: Vec::new(),
                                        budget: state.budget,
                                        cut_executed: false,
                                    };
                                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &matched_env)?;
                                    state.budget = sub_budget;
                                    results.extend(res);
                                    match exit_status {
                                        VmExit::Cut => {
                                            state.cut_executed = true;
                                            break;
                                        }
                                        VmExit::TailCall(new_locals) => {
                                            return Ok((results, state.budget, VmExit::TailCall(new_locals)));
                                        }
                                        VmExit::Normal => {}
                                    }
                                }
                                None => {}
                            }
                        }
                    }

                    if !matched_any {
                        let mut sub_state = VMState::new_with_parent(
                            else_code.clone(),
                            free_vars_map.clone(),
                            state.budget,
                            &state.free_vars_map,
                            &state.free_vars_bindings,
                        );
                        for val in &state.locals {
                            sub_state.locals.push(val.clone());
                        }
                        let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &current_env)?;
                        state.budget = sub_budget;
                        results.extend(res);
                        match exit_status {
                            VmExit::Cut => { state.cut_executed = true; }
                            VmExit::TailCall(new_locals) => {
                                return Ok((results, state.budget, VmExit::TailCall(new_locals)));
                            }
                            VmExit::Normal => {}
                        }
                    }
                }

                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::Call(arity) => {
                let head_rs = state.stack.pop().ok_or("VM stack underflow on Call head")?;
                let mut arg_sets = Vec::with_capacity(*arity as usize);
                for _ in 0..*arity {
                    arg_sets.push(state.stack.pop().ok_or("VM stack underflow on Call arg")?);
                }
                arg_sets.reverse();
                
                let mut sets = vec![head_rs];
                sets.extend(arg_sets);
                let full_combos = super::super::budget::threaded_combinations(&sets);
                
                let mut pending_calls = Vec::new();
                let mut results = Vec::new();
                
                let mut call_memo_key = None;
                for (combo, combo_env) in &full_combos {
                    if combo.is_empty() { continue; }
                    let head_atom = &combo[0];
                    let args = &combo[1..];
                    
                    let mut memo_key_out = None;
                    dispatch_call(
                        head_atom,
                        args,
                        *arity,
                        combo_env,
                        funcs,
                        &mut results,
                        &mut pending_calls,
                        &mut memo_key_out,
                    )?;
                    if full_combos.len() == 1 {
                        call_memo_key = memo_key_out;
                    }
                }
                
                // skip frame when no pending calls (native functions / partial applications fully resolved).
                // Pushing an empty frame and immediately popping it would restore an empty
                // saved_locals, clearing the function's actual state.locals.
                if pending_calls.is_empty() {
                    // Must advance ip past Call opcode since no frame will restore return_ip.
                    state.ip += 1;
                    let results = std::mem::take(&mut results);
                    state.stack.push(results);
                    continue;
                }
                
                let frame = CallFrame {
                    return_ip: state.ip,
                    return_code: state.code.clone(),
                    locals_to_pop: 0,
                    saved_base_env: base_env.clone(),
                    saved_locals: Vec::new(),
                    saved_free_vars_map: state.free_vars_map.clone(),
                    saved_free_vars_bindings: state.free_vars_bindings.clone(),
                    kind: CallFrameKind::Call {
                        name: match full_combos.first().and_then(|c| c.0.first()) {
                            Some(Atom::Sym(s)) => intern_name(s),
                            _ => "",
                        },
                        arity: *arity,
                        pending_calls,
                        next_idx: 0,
                        results,
                        memo_key: call_memo_key,
                    },
                };
                state.frames.push(frame);
                if let Some(next_env) = run_next_call_iteration(&mut state, funcs)? {
                    base_env = next_env;
                }
                continue;
            }
            Opcode::DebitBudget(cost) => {
                if let Some(b) = state.budget {
                    if b <= *cost {
                        return Err("Budget exhausted".into());
                    }
                    state.budget = Some(b - *cost);
                }
                state.ip += 1;
            }
            Opcode::Collapse => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Collapse"))
                } else {
                    None
                };
                let val_rs = state.stack.pop().ok_or("VM stack underflow on Collapse")?;
                // substitute environment variables on collapse
                let atoms: Vec<Atom> = val_rs.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(atoms))]));
                state.ip += 1;
            }
            Opcode::Test => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Test"))
                } else {
                    None
                };
                // Pop expected (evaluated second, so on top)
                let expected_rs = state.stack.pop().ok_or("VM stack underflow on Test expected")?;
                // Pop expression results (evaluated first)
                let expr_rs = state.stack.pop().ok_or("VM stack underflow on Test expr")?;

                // Collect ALL atoms from the expression result set (like PeTTa's findall)
                // substitute environments to resolve variables before comparison
                let expr_atoms: Vec<Atom> = expr_rs.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();

                // If single result, use directly; if multiple or empty, use as list
                let actual = if expr_atoms.len() == 1 {
                    expr_atoms.into_iter().next().unwrap()
                } else {
                    Atom::Expr(crate::atom::expr_data(expr_atoms))
                };

                // Expected value: take the first result
                // substitute expected environment as well
                let expected_atoms: Vec<Atom> = expected_rs.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                let expected = if expected_atoms.len() == 1 {
                    expected_atoms.into_iter().next().unwrap()
                } else {
                    Atom::Expr(crate::atom::expr_data(expected_atoms))
                };

                let eq = actual == expected;
                let emoji = if eq { "✅" } else { "❌" };
                eprintln!("is {}, should {}. {} ", actual.to_sexpr_string(), expected.to_sexpr_string(), emoji);

                state.stack.push(plain(vec![crate::atom::Atom::sym("true")]));
                state.ip += 1;
            }
            Opcode::Superpose(count) => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Superpose"))
                } else {
                    None
                };
                let mut results = Vec::new();
                let mut popped = Vec::with_capacity(*count as usize);
                for _ in 0..*count {
                    popped.push(state.stack.pop().ok_or("VM stack underflow on Superpose")?);
                }
                popped.reverse();
                for rs in popped {
                    results.extend(rs);
                }
                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::SuperposeUnpack => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("SuperposeUnpack"))
                } else {
                    None
                };
                let val_rs = state.stack.pop().ok_or("VM stack underflow on SuperposeUnpack")?;
                if let Some((first, _)) = val_rs.first() {
                    match first {
                        Atom::Expr(elements) => {
                            state.stack.push(plain(elements.to_vec()));
                        }
                        other => {
                            state.stack.push(plain(vec![other.clone()]));
                        }
                    }
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::ConstEmpty => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("ConstEmpty"))
                } else {
                    None
                };
                state.stack.push(Vec::new());
                state.ip += 1;
            }
            Opcode::Cut => {
                state.stack.push(plain(vec![Atom::sym("true")]));
                state.cut_executed = true;
                state.ip += 1;
            }
            Opcode::Println => {
                let arg_rs = state.stack.pop().ok_or("VM stack underflow on Println")?;
                let res = crate::eval::io::finish_println(arg_rs);
                state.stack.push(res);
                state.ip += 1;
            }
            Opcode::Readln => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Readln"))
                } else {
                    None
                };
                let nd = crate::eval::io::eval_readln(&[], &base_env, funcs)?;
                state.stack.push(plain(nd.collect()));
                state.ip += 1;
            }
            Opcode::Match {
                pattern,
                body_code,
                local_names,
                pattern_vars,
                free_vars_map,
            } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Match"))
                } else {
                    None
                };
                let space_rs = state.stack.pop().ok_or("VM stack underflow on Match space")?;
                let mut results = Vec::new();
                if let Some((space_ref, _)) = space_rs.first() {
                    let mut match_env = Env::new();
                    for (name, val) in local_names.iter().zip(state.locals.iter()) {
                        match_env = match_env.extend(name, val.0.clone());
                    }
                    
                    if let Ok(matches) = crate::space::query::collect_match_results(
                        funcs,
                        space_ref,
                        pattern,
                        &match_env,
                    ) {
                        if !matches.is_empty() {
                            // Precompute bindings once for the entire Match block
                            let precomputed_bindings: Vec<Atom> = free_vars_map
                                .iter()
                                .map(|name| {
                                    if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                                        state.free_vars_bindings[pos].clone()
                                    } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                                        Atom::sym(name)
                                    } else {
                                        let id = crate::eval::machine::vm::state::next_fresh_id();
                                        let hint = name.strip_prefix('$').unwrap_or(name);
                                        let fresh_name = format!("$__fresh_{hint}_{id}");
                                        Atom::sym(&fresh_name)
                                    }
                                })
                                .collect();

                            for matched in matches {
                                let mut sub_state_locals = Vec::with_capacity(state.locals.len() + pattern_vars.len());
                                for val in &state.locals {
                                    sub_state_locals.push(val.clone());
                                }
                                for var in pattern_vars {
                                    let bound = matched.bindings.iter()
                                        .find(|(k, _)| k.as_ref() == var.as_str())
                                        .map(|(_, v)| (**v).clone())
                                        .unwrap_or_else(|| {
                                            if let Some(idx) = local_names.iter().position(|x| x == var) {
                                                state.locals[idx].0.clone()
                                            } else {
                                                Atom::sym("()")
                                            }
                                        });
                                    sub_state_locals.push((bound, Env::new()));
                                }
                                
                                let sub_state = VMState {
                                    code: body_code.clone(),
                                    ip: 0,
                                    stack: Vec::new(),
                                    locals: sub_state_locals,
                                    free_vars_map: free_vars_map.clone(),
                                    free_vars_bindings: precomputed_bindings.clone(),
                                    frames: Vec::new(),
                                    budget: state.budget,
                                    cut_executed: false,
                                };
                                
                                let sub_env = crate::eval::shared::env::bind_all(&match_env, &matched.bindings);
                                let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &sub_env)?;
                                state.budget = sub_budget;
                                results.extend(res);
                                match exit_status {
                                    VmExit::Cut => {
                                        state.cut_executed = true;
                                        break;
                                    }
                                    VmExit::TailCall(new_locals) => {
                                        return Ok((results, state.budget, VmExit::TailCall(new_locals)));
                                    }
                                    VmExit::Normal => {}
                                }
                            }
                        }
                    }
                }
                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::Eval => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Eval"))
                } else {
                    None
                };
                let val_rs = state.stack.pop().ok_or("VM stack underflow on Eval")?;
                let mut target_rs = Vec::new();
                for (atom, env) in val_rs {
                    let (target_expr, target_env) = match &atom {
                        Atom::Closure(c) if c.params.is_empty() => {
                            (c.body.clone(), c.env.clone())
                        }
                        other => {
                            let expr = crate::parser::atom_to_expr(other)?;
                            (expr, env.clone())
                        }
                    };
                    target_rs.push((target_expr, target_env));
                }
                
                let frame = CallFrame {
                    return_ip: state.ip,
                    return_code: state.code.clone(),
                    locals_to_pop: 0,
                    saved_base_env: base_env.clone(),
                    saved_locals: Vec::new(),
                    saved_free_vars_map: state.free_vars_map.clone(),
                    saved_free_vars_bindings: state.free_vars_bindings.clone(),
                    kind: CallFrameKind::Eval {
                        target_rs,
                        next_idx: 0,
                        results: Vec::new(),
                    },
                };
                state.frames.push(frame);
                if let Some(next_env) = run_next_eval_iteration(&mut state, funcs)? {
                    base_env = next_env;
                }
                continue;
            }
            Opcode::If { then_code, else_code, free_vars_map } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("If"))
                } else {
                    None
                };
                let condition_rs = state.stack.pop().ok_or("VM stack underflow on If")?;
                let frame = CallFrame {
                    return_ip: state.ip,
                    return_code: state.code.clone(),
                    locals_to_pop: 0,
                    saved_base_env: base_env.clone(),
                    saved_locals: Vec::new(),
                    saved_free_vars_map: state.free_vars_map.clone(),
                    saved_free_vars_bindings: state.free_vars_bindings.clone(),
                    kind: CallFrameKind::If {
                        condition_rs: condition_rs.into_iter().collect(),
                        next_idx: 0,
                        then_code: then_code.clone(),
                        else_code: else_code.clone(),
                        free_vars_map: free_vars_map.clone(),
                        results: Vec::new(),
                    },
                };
                state.frames.push(frame);
                if let Some(next_env) = run_next_if_iteration(&mut state)? {
                    base_env = next_env;
                }
                continue;
            }
            Opcode::Let {
                pattern,
                body_code,
                pattern_vars,
                free_vars_map,
            } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Let"))
                } else {
                    None
                };
                let value_rs = state.stack.pop().ok_or("VM stack underflow on Let")?;
                let frame = CallFrame {
                    return_ip: state.ip,
                    return_code: state.code.clone(),
                    locals_to_pop: 0,
                    saved_base_env: base_env.clone(),
                    saved_locals: Vec::new(),
                    saved_free_vars_map: state.free_vars_map.clone(),
                    saved_free_vars_bindings: state.free_vars_bindings.clone(),
                    kind: CallFrameKind::Let {
                        value_rs,
                        next_idx: 0,
                        pattern: pattern.clone(),
                        pattern_vars: pattern_vars.clone(),
                        free_vars_map: free_vars_map.clone(),
                        body_code: body_code.clone(),
                        results: Vec::new(),
                    },
                };
                state.frames.push(frame);
                if let Some(next_env) = run_next_let_iteration(&mut state, funcs)? {
                    base_env = next_env;
                }
                continue;
            }
            Opcode::Case { branches, local_names } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Case"))
                } else {
                    None
                };
                let scrutinee_rs = state.stack.pop().ok_or("VM stack underflow on Case")?;
                let frame = CallFrame {
                    return_ip: state.ip,
                    return_code: state.code.clone(),
                    locals_to_pop: 0,
                    saved_base_env: base_env.clone(),
                    saved_locals: Vec::new(),
                    saved_free_vars_map: state.free_vars_map.clone(),
                    saved_free_vars_bindings: state.free_vars_bindings.clone(),
                    kind: CallFrameKind::Case {
                        scrutinee_rs: scrutinee_rs.into_iter().collect(),
                        next_idx: 0,
                        branches: branches.clone(),
                        results: Vec::new(),
                    },
                };
                state.frames.push(frame);
                if let Some(next_env) = run_next_case_iteration(&mut state, funcs)? {
                    base_env = next_env;
                }
                continue;
            }
            Opcode::Foldall => {
                // Foldall pops agg-func, init, and generator, then loops using eval_call_vm
                let agg_rs = state.stack.pop().ok_or("VM stack underflow on Foldall agg-func")?;
                let init_rs = state.stack.pop().ok_or("VM stack underflow on Foldall init")?;
                let gen_rs = state.stack.pop().ok_or("VM stack underflow on Foldall generator")?;

                // substitute environments to resolve variables
                let agg_atom = agg_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "foldall: agg-func produced no value".to_string())?;
                let init_atom = init_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "foldall: init produced no result".to_string())?;
                let gen_values: Vec<Atom> = gen_rs.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();

                let (agg_head, agg_env) = match &agg_atom {
                    Atom::Sym(name) => {
                        (Expr::Symbol(name.to_string()), base_env.clone())
                    }
                    Atom::Closure(_) => {
                        (Expr::Symbol("$__foldall_fn".to_string()),
                         crate::eval::shared::env::bind(&base_env, "$__foldall_fn", agg_atom.clone()))
                    }
                    _ => return Err("foldall: agg-func must be a function symbol or closure".to_string()),
                };

                let mut accum = init_atom;
                for val in gen_values {
                    let acc_expr = crate::parser::atom_to_expr(&accum)?;
                    let val_expr = crate::parser::atom_to_expr(&val)?;
                    let res = eval_call_vm(
                        agg_head.clone(),
                        vec![acc_expr, val_expr],
                        &agg_env,
                        funcs,
                        &mut state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    )?;
                    // substitute env
                    accum = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                        .ok_or_else(|| "foldall: agg-func produced no result".to_string())?;
                }
                state.stack.push(plain(vec![accum]));
                state.ip += 1;
            }
            Opcode::Forall => {
                // Forall pops check-expr and generator, then verifies truthiness for all values
                let check_rs = state.stack.pop().ok_or("VM stack underflow on Forall check")?;
                let gen_rs = state.stack.pop().ok_or("VM stack underflow on Forall generator")?;

                // substitute env
                let check_atom = check_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "forall: check produced no value".to_string())?;
                let gen_values: Vec<Atom> = gen_rs.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();

                let check_head = match &check_atom {
                    Atom::Sym(name) => Expr::Symbol(name.to_string()),
                    Atom::Closure(_) => Expr::Symbol("$__check_fn".to_string()),
                    _ => return Err("forall: check must be a function symbol or closure".to_string()),
                };

                let mut is_forall_true = true;
                for val in gen_values {
                    let mut call_env = crate::eval::shared::env::bind(&base_env, "$__fv", val);
                    if let Atom::Closure(_) = &check_atom {
                        let check_env = crate::eval::shared::env::bind(&base_env, "$__check_fn", check_atom.clone());
                        call_env = crate::eval::shared::pattern::prepend_env(check_env, &call_env);
                    }
                    let res = eval_call_vm(
                        check_head.clone(),
                        vec![Expr::Symbol("$__fv".to_string())],
                        &call_env,
                        funcs,
                        &mut state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    )?;
                    // substitute env
                    let results: Vec<Atom> = res.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                    if results.is_empty() || !results.iter().all(|a| crate::eval::forms::control::is_truthy(a)) {
                        is_forall_true = false;
                        break;
                    }
                }
                let final_atom = if is_forall_true { Atom::sym("true") } else { Atom::sym("false") };
                state.stack.push(plain(vec![final_atom]));
                state.ip += 1;
            }
            Opcode::Foldl => {
                // Foldl pops func, acc, and list, and folds dynamically
                let func_rs = state.stack.pop().ok_or("VM stack underflow on Foldl func")?;
                let acc_rs = state.stack.pop().ok_or("VM stack underflow on Foldl acc")?;
                let list_rs = state.stack.pop().ok_or("VM stack underflow on Foldl list")?;

                // substitute environments to resolve variables
                let func = func_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "foldl-atom: func arg produced no result".to_string())?;
                let acc = acc_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("foldl-atom: list arg produced no result".to_string()),
                };

                let mut current_acc = acc;
                let func_head = match &func {
                    Atom::Sym(name) => Expr::Symbol(name.to_string()),
                    _ => crate::parser::atom_to_expr(&func)
                        .unwrap_or_else(|_| Expr::Symbol(func.to_sexpr_string())),
                };
                for item in items {
                    let acc_expr = crate::parser::atom_to_expr(&current_acc)
                        .unwrap_or_else(|_| Expr::Symbol(current_acc.to_sexpr_string()));
                    let item_expr = crate::parser::atom_to_expr(&item)
                        .unwrap_or_else(|_| Expr::Symbol(item.to_sexpr_string()));
                    let res = eval_call_vm(
                        func_head.clone(),
                        vec![acc_expr, item_expr],
                        &Env::new(),
                        funcs,
                        &mut state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    )?;
                    // substitute env
                    current_acc = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).unwrap_or(current_acc);
                }
                state.stack.push(plain(vec![current_acc]));
                state.ip += 1;
            }
            Opcode::FoldlLambda {
                var_names,
                body_code,
                free_vars_map,
            } => {
                // FoldlLambda aggregates list elements using a precompiled lambda body code for high performance
                let acc_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda acc")?;
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda list")?;

                // substitute env
                let acc = acc_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("foldl-atom: list arg produced no result".to_string()),
                };

                let mut current_acc = acc;
                for elem in items {
                    let mut sub_state = VMState::new_with_parent(
                        body_code.clone(),
                        free_vars_map.clone(),
                        state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    );
                    for val in &state.locals {
                        sub_state.locals.push(val.clone());
                    }
                    let vals_to_bind = [current_acc.clone(), elem];
                    for (var, val) in var_names.iter().zip(vals_to_bind.iter()) {
                        sub_state.locals.push((val.clone(), Env::new()));
                    }
                    if var_names.len() > vals_to_bind.len() {
                        for _ in vals_to_bind.len()..var_names.len() {
                            sub_state.locals.push((Atom::sym("()"), Env::new()));
                        }
                    }
                    let mut step_env = base_env.clone();
                    for (var, val) in var_names.iter().zip(vals_to_bind.iter()) {
                        step_env = step_env.extend(var, val.clone());
                    }
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &step_env)?;
                    state.budget = sub_budget;
                    // substitute env
                    current_acc = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).unwrap_or(current_acc);
                    match exit_status {
                        VmExit::Cut => {
                            state.cut_executed = true;
                            break;
                        }
                        VmExit::TailCall(new_locals) => {
                            return Ok((plain(vec![current_acc]), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Normal => {}
                    }
                }
                state.stack.push(plain(vec![current_acc]));
                state.ip += 1;
            }
            Opcode::MapAtomLambda {
                var_name,
                body_code,
                free_vars_map,
            } => {
                // MapAtomLambda maps list elements using a precompiled lambda body code for high performance
                let list_rs = state.stack.pop().ok_or("VM stack underflow on MapAtomLambda")?;
                // substitute env to resolve variables in list argument
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("map-atom: list arg produced no result".to_string()),
                };

                let mut mapped_results = Vec::with_capacity(items.len());
                for elem in items {
                    let mut sub_state = VMState::new_with_parent(
                        body_code.clone(),
                        free_vars_map.clone(),
                        state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    );
                    for val in &state.locals {
                        sub_state.locals.push(val.clone());
                    }
                    sub_state.locals.push((elem.clone(), Env::new()));
                    
                    let sub_env = base_env.extend(&var_name, elem.clone());
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &sub_env)?;
                    state.budget = sub_budget;
                    
                    // substitute env for mapped item
                    if let Some((val, env)) = res.into_iter().next() {
                        mapped_results.push(crate::eval::shared::subst::subst_atom(&val, &env));
                    }
                    match exit_status {
                        VmExit::Cut => {
                            state.cut_executed = true;
                            break;
                        }
                        VmExit::TailCall(new_locals) => {
                            return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(mapped_results))]), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Normal => {}
                    }
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(mapped_results))]));
                state.ip += 1;
            }
            Opcode::FilterAtomLambda {
                var_name,
                body_code,
                free_vars_map,
            } => {
                // FilterAtomLambda filters list elements using a precompiled lambda condition code for high performance
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FilterAtomLambda")?;
                // substitute env to resolve variables in list argument
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("filter-atom: list arg produced no result".to_string()),
                };

                let mut filtered_results = Vec::with_capacity(items.len());
                for elem in items {
                    let mut sub_state = VMState::new_with_parent(
                        body_code.clone(),
                        free_vars_map.clone(),
                        state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    );
                    for val in &state.locals {
                        sub_state.locals.push(val.clone());
                    }
                    sub_state.locals.push((elem.clone(), Env::new()));
                    
                    let sub_env = base_env.extend(&var_name, elem.clone());
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &sub_env)?;
                    state.budget = sub_budget;
                    
                    // substitute env
                    let is_true = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).is_truthy()).unwrap_or(false);
                    if is_true {
                        filtered_results.push(elem);
                    }
                    match exit_status {
                        VmExit::Cut => {
                            state.cut_executed = true;
                            break;
                        }
                        VmExit::TailCall(new_locals) => {
                            return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(filtered_results))]), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Normal => {}
                    }
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(filtered_results))]));
                state.ip += 1;
            }
            Opcode::Once { body_code, free_vars_map } => {
                // run body, take only the first result
                let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                for val in &state.locals { sub_state.locals.push(val.clone()); }
                let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                state.budget = sub_budget;
                match exit_status {
                    VmExit::TailCall(new_locals) => {
                        return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                    }
                    VmExit::Cut => {
                        state.stack.push(res.into_iter().take(1).collect());
                        state.cut_executed = true;
                    }
                    VmExit::Normal => {
                        state.stack.push(res.into_iter().take(1).collect());
                    }
                }
                state.ip += 1;
            }
            Opcode::Progn { bodies, free_vars_map } => {
                // run each body, return last result
                let mut last = Vec::new();
                for body_code in bodies {
                    let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    for val in &state.locals { sub_state.locals.push(val.clone()); }
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                    state.budget = sub_budget;
                    match exit_status {
                        VmExit::TailCall(new_locals) => {
                            return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Cut => {
                            last = res;
                            state.cut_executed = true;
                            break;
                        }
                        VmExit::Normal => {
                            last = res;
                        }
                    }
                }
                state.stack.push(last);
                state.ip += 1;
            }
            Opcode::Prog1 { bodies, free_vars_map } => {
                // run each body, return first result
                let mut first = Vec::new();
                for (i, body_code) in bodies.iter().enumerate() {
                    let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    for val in &state.locals { sub_state.locals.push(val.clone()); }
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                    state.budget = sub_budget;
                    match exit_status {
                        VmExit::TailCall(new_locals) => {
                            return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Cut => {
                            if i == 0 { first = res; }
                            state.cut_executed = true;
                            break;
                        }
                        VmExit::Normal => {
                            if i == 0 { first = res; }
                        }
                    }
                }
                state.stack.push(first);
                state.ip += 1;
            }
            Opcode::Chain { steps, final_code, free_vars_map } => {
                // evaluate each step, bind result into parent free_vars so new_with_parent threads them through
                for (step_code, var_name) in steps.iter() {
                    let mut sub_state = VMState::new_with_parent(step_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    for val in &state.locals { sub_state.locals.push(val.clone()); }
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                    state.budget = sub_budget;
                    
                    let val: Atom = match exit_status {
                        VmExit::TailCall(new_locals) => {
                            return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Cut => {
                            state.cut_executed = true;
                            // substitute env to preserve variables
                            res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                        }
                        VmExit::Normal => {
                            // substitute env to preserve variables
                            res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                        }
                    }.ok_or_else(|| format!("chain: expression for {} produced no result", var_name))?;
                    
                    // Inject into parent so subsequent steps and final body inherit the binding
                    if let Some(pos) = state.free_vars_map.iter().position(|x| x == var_name) {
                        state.free_vars_bindings[pos] = val;
                    } else {
                        let mut temp = state.free_vars_map.to_vec();
                        temp.push(var_name.clone());
                        state.free_vars_map = std::sync::Arc::from(temp);
                        state.free_vars_bindings.push(val);
                    }
                    if state.cut_executed { break; }
                }
                if !state.cut_executed {
                    let mut sub_state = VMState::new_with_parent(final_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    for val in &state.locals { sub_state.locals.push(val.clone()); }
                    let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                    state.budget = sub_budget;
                    match exit_status {
                        VmExit::TailCall(new_locals) => {
                            return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                        }
                        VmExit::Cut => {
                            state.cut_executed = true;
                            state.stack.push(res);
                        }
                        VmExit::Normal => {
                            state.stack.push(res);
                        }
                    }
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::Within { body_code, free_vars_map } => {
                // run body, collect all results, wrap into (within result1 result2 ...)
                let mut sub_state = VMState::new_with_parent(
                    body_code.clone(),
                    free_vars_map.clone(),
                    state.budget,
                    &state.free_vars_map,
                    &state.free_vars_bindings,
                );
                for val in &state.locals { sub_state.locals.push(val.clone()); }
                let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &base_env)?;
                state.budget = sub_budget;
                match exit_status {
                    VmExit::TailCall(new_locals) => {
                        return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                    }
                    VmExit::Cut => {
                        state.cut_executed = true;
                    }
                    VmExit::Normal => {}
                }
                // substitute env on Within to resolve variables
                let atoms: Vec<Atom> = res.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                if atoms.is_empty() {
                    return Err("within: expression produced no results".into());
                }
                let wrapped = Atom::Expr(crate::atom::expr_data(
                    std::iter::once(Atom::sym("within")).chain(atoms).collect::<Vec<_>>()
                ));
                state.stack.push(plain(vec![wrapped]));
                state.ip += 1;
            }
            Opcode::WithMutex { body_code, free_vars_map } => {
                // pop evaluated mutex name, acquire named lock, run body, release
                let name_rs = state.stack.pop().ok_or("VM stack underflow on WithMutex")?;
                // substitute env
                let mutex_name = name_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).to_sexpr_string()).unwrap_or_default();
                let mut sub_state = VMState::new_with_parent(
                    body_code.clone(),
                    free_vars_map.clone(),
                    state.budget,
                    &state.free_vars_map,
                    &state.free_vars_bindings,
                );
                for val in &state.locals { sub_state.locals.push(val.clone()); }
                let result = crate::space::mutate::with_named_mutex(&mutex_name, || {
                    run_vm(sub_state, funcs, &base_env)
                })?;
                let (res, sub_budget, exit_status) = result;
                state.budget = sub_budget;
                match exit_status {
                    VmExit::TailCall(new_locals) => {
                        return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                    }
                    VmExit::Cut => {
                        state.cut_executed = true;
                    }
                    VmExit::Normal => {}
                }
                state.stack.push(res);
                state.ip += 1;
            }
            Opcode::Transaction { body_code, free_vars_map } => {
                // snapshot state, run body in sub-VM, rollback on empty result or error
                let snapshot = crate::space::mutate::snapshot_transaction_state(funcs);
                let mut sub_state = VMState::new_with_parent(
                    body_code.clone(),
                    free_vars_map.clone(),
                    state.budget,
                    &state.free_vars_map,
                    &state.free_vars_bindings,
                );
                for val in &state.locals { sub_state.locals.push(val.clone()); }
                match run_vm(sub_state, funcs, &base_env) {
                    Ok((res, sub_budget, exit_status)) => {
                        state.budget = sub_budget;
                        match exit_status {
                            VmExit::TailCall(new_locals) => {
                                crate::space::mutate::restore_transaction_state(snapshot, funcs)
                                    .map_err(|e| format!("transaction: rollback failed: {e}"))?;
                                return Ok((Vec::new(), state.budget, VmExit::TailCall(new_locals)));
                            }
                            VmExit::Cut => {
                                state.cut_executed = true;
                            }
                            VmExit::Normal => {}
                        }
                        if res.is_empty() {
                            crate::space::mutate::restore_transaction_state(snapshot, funcs)
                                .map_err(|e| format!("transaction: rollback failed: {e}"))?;
                        }
                        state.stack.push(res);
                    }
                    Err(err) => {
                        crate::space::mutate::restore_transaction_state(snapshot, funcs)
                            .map_err(|e| format!("transaction: rollback failed: {e}"))?;
                        return Err(format!("transaction: {err}"));
                    }
                }
                state.ip += 1;
            }
            Opcode::ImportFile { path } => {
                // reuse existing apply.rs Frame::ImportFile logic directly
                let space_rs = state.stack.pop().ok_or("VM stack underflow on ImportFile")?;
                // substitute env
                let space_ref = space_rs
                    .into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .unwrap_or_else(|| Atom::sym("&self"));
                let import_dir = funcs.import_dir.lock().unwrap().clone();
                let resolved = crate::eval::io::resolve_import_path(&path, &import_dir)
                    .ok_or_else(|| format!("import!: cannot find '{}' (searched CWD and '{}')", path, import_dir.display()))?;
                let new_dir = resolved.parent().unwrap_or(std::path::Path::new(".")).to_path_buf();
                let prev_dir = std::mem::replace(&mut *funcs.import_dir.lock().unwrap(), new_dir);
                let atoms = crate::eval::io::load_metta_file(&resolved, &space_ref, &base_env, funcs)?;
                *funcs.import_dir.lock().unwrap() = prev_dir;
                state.stack.push(plain(atoms));
                state.ip += 1;
            }
            Opcode::PythonImport { path } => {
                // reuse existing apply.rs Frame::PythonImport logic directly
                let _space_rs = state.stack.pop(); // space-ref consumed but unused for Python
                let import_dir = funcs.import_dir.lock().unwrap().clone();
                let py_path = std::path::Path::new(&path);
                let resolved = if py_path.exists() {
                    Some(py_path.to_path_buf())
                } else {
                    let with_ext = format!("{}.py", path);
                    let candidates = [
                        std::path::PathBuf::from(&with_ext),
                        import_dir.join(&path),
                        import_dir.join(&with_ext),
                    ];
                    candidates.into_iter().find(|p| p.exists())
                }
                .ok_or_else(|| format!("import!: cannot find Python file '{}' (searched CWD and '{}')", path, import_dir.display()))?;
                crate::eval::python::eval_py_import_library(&resolved)?;
                state.stack.push(plain(vec![Atom::sym("true")]));
                state.ip += 1;
            }
            Opcode::PyCall { expr } => {
                // Direct VM opcode for py-call — bypasses dispatch.rs entirely.
                let result = crate::eval::python::eval_py_call(&[expr.clone()], &base_env, funcs)?;
                let atoms: Vec<Atom> = result.collect();
                state.stack.push(plain(atoms));
                state.ip += 1;
            }
            Opcode::PyEval { expr } => {
                match crate::eval::python::eval_py_eval(&[expr.clone()], &base_env, funcs) {
                    Ok(nd) => {
                        state.stack.push(plain(nd.collect()));
                    }
                    Err(e) => return Err(e),
                }
                state.ip += 1;
            }
            Opcode::ImportDynamic => {
                let path_rs = state.stack.pop().ok_or("VM stack underflow on ImportDynamic path")?;
                let space_rs = state.stack.pop().ok_or("VM stack underflow on ImportDynamic space")?;

                // substitute env
                let path = match path_rs.first().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Sym(s)) | Some(Atom::Str(s)) => s.clone(),
                    Some(Atom::Expr(expr)) if expr.len() == 2 => {
                        if let (Some(Atom::Sym(head)), Some(py_atom)) = (expr.get(0), expr.get(1)) {
                            if head.as_ref() == "library" {
                                match py_atom {
                                    Atom::Sym(py) | Atom::Str(py) => py.clone(),
                                    _ => return Err("import!: invalid path expression".into()),
                                }
                            } else {
                                return Err("import!: invalid path expression".into());
                            }
                        } else {
                            return Err("import!: invalid path expression".into());
                        }
                    }
                    _ => return Err("import!: path must be a symbol or string".into()),
                };

                // substitute env
                let space_ref = space_rs.first().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                    .unwrap_or_else(|| Atom::sym("&self"));

                let is_py = path.ends_with(".py");
                if is_py {
                    let import_dir = funcs.import_dir.lock().unwrap().clone();
                    let py_path = std::path::Path::new(path.as_ref());
                    let resolved = if py_path.exists() {
                        Some(py_path.to_path_buf())
                    } else {
                        let with_ext = format!("{}.py", path);
                        let py_ext = std::path::Path::new(&with_ext);
                        if py_ext.exists() {
                            Some(py_ext.to_path_buf())
                        } else {
                            let in_dir = import_dir.join(path.as_ref());
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
                    state.stack.push(plain(vec![Atom::sym("true")]));
                } else {
                    let import_dir = funcs.import_dir.lock().unwrap().clone();
                    let resolved = crate::eval::io::resolve_import_path(path.as_ref(), &import_dir)
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
                    let atoms = crate::eval::io::load_metta_file(&resolved, &space_ref, &base_env, funcs)?;
                    *funcs.import_dir.lock().unwrap() = prev_dir;
                    state.stack.push(plain(atoms));
                }
                state.ip += 1;
            }
            Opcode::MapAtomPatternLambda {
                pattern,
                body_code,
                pattern_vars,
                free_vars_map,
            } => {
                let list_rs = state.stack.pop().ok_or("VM stack underflow on MapAtomPatternLambda")?;
                // substitute env
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("map-atom: list arg produced no result".to_string()),
                };

                let mut mapped_results = Vec::with_capacity(items.len());
                for elem in items {
                    let matched = crate::eval::shared::pattern::try_match_one(
                        pattern, &elem, &base_env, funcs,
                    )?;
                    if let Some(matched_env) = matched {
                        let mut sub_state = VMState::new_with_parent(
                            body_code.clone(),
                            free_vars_map.clone(),
                            state.budget,
                            &state.free_vars_map,
                            &state.free_vars_bindings,
                        );
                        for val in &state.locals {
                            sub_state.locals.push(val.clone());
                        }
                        for var in pattern_vars {
                            let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                            sub_state.locals.push((bound, Env::new()));
                        }
                        let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &matched_env)?;
                        state.budget = sub_budget;

                        // substitute env
                        if let Some((val, env)) = res.into_iter().next() {
                            mapped_results.push(crate::eval::shared::subst::subst_atom(&val, &env));
                        }
                        match exit_status {
                            VmExit::Cut => {
                                state.cut_executed = true;
                                break;
                            }
                            VmExit::TailCall(new_locals) => {
                                return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(mapped_results))]), state.budget, VmExit::TailCall(new_locals)));
                            }
                            VmExit::Normal => {}
                        }
                    }
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(mapped_results))]));
                state.ip += 1;
            }
            Opcode::FilterAtomPatternLambda {
                pattern,
                body_code,
                pattern_vars,
                free_vars_map,
            } => {
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FilterAtomPatternLambda")?;
                // substitute env
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("filter-atom: list arg produced no result".to_string()),
                };

                let mut filtered_results = Vec::with_capacity(items.len());
                for elem in items {
                    let matched = crate::eval::shared::pattern::try_match_one(
                        pattern, &elem, &base_env, funcs,
                    )?;
                    if let Some(matched_env) = matched {
                        let mut sub_state = VMState::new_with_parent(
                            body_code.clone(),
                            free_vars_map.clone(),
                            state.budget,
                            &state.free_vars_map,
                            &state.free_vars_bindings,
                        );
                        for val in &state.locals {
                            sub_state.locals.push(val.clone());
                        }
                        for var in pattern_vars {
                            let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                            sub_state.locals.push((bound, Env::new()));
                        }
                        let (res, sub_budget, exit_status) = run_vm(sub_state, funcs, &matched_env)?;
                        state.budget = sub_budget;

                        // substitute env
                        let is_true = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).is_truthy()).unwrap_or(false);
                        if is_true {
                            filtered_results.push(elem);
                        }
                        match exit_status {
                            VmExit::Cut => {
                                state.cut_executed = true;
                                break;
                            }
                            VmExit::TailCall(new_locals) => {
                                return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(filtered_results))]), state.budget, VmExit::TailCall(new_locals)));
                            }
                            VmExit::Normal => {}
                        }
                    }
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(filtered_results))]));
                state.ip += 1;
            }
            Opcode::TailCallSelf => {
                let mut has_choice_points = false;
                let mut call_frame_idx = None;
                for (i, frame) in state.frames.iter().enumerate().rev() {
                    match &frame.kind {
                        CallFrameKind::Normal => {}
                        CallFrameKind::Let { value_rs, next_idx, .. } => {
                            if *next_idx < value_rs.len() {
                                has_choice_points = true;
                            }
                        }
                        CallFrameKind::If { condition_rs, next_idx, .. } => {
                            if *next_idx < condition_rs.len() {
                                has_choice_points = true;
                            }
                        }
                        CallFrameKind::Case { scrutinee_rs, next_idx, .. } => {
                            if *next_idx < scrutinee_rs.len() {
                                has_choice_points = true;
                            }
                        }
                        CallFrameKind::Call { pending_calls, next_idx, .. } => {
                            call_frame_idx = Some(i);
                            if *next_idx < pending_calls.len() {
                                has_choice_points = true;
                            }
                            break;
                        }
                        CallFrameKind::Eval { target_rs, next_idx, .. } => {
                            if *next_idx < target_rs.len() {
                                has_choice_points = true;
                            }
                        }
                    }
                }

                if has_choice_points {
                    if let Some(c_idx) = call_frame_idx {
                        let (arity, name) = match &state.frames[c_idx].kind {
                            CallFrameKind::Call { arity, name, .. } => (*arity, *name),
                            _ => unreachable!(),
                        };
                        let new_args: Vec<Atom> = state.locals.iter().take(arity as usize).map(|(atom, _)| atom.clone()).collect();
                        let mut pending_calls = Vec::new();
                        if let Some(clauses) = crate::eval::forms::query::lookup_user_clauses(name, arity, funcs) {
                            let cache_key = (name.to_string(), arity);
                            let cached = FN_BYTECODE_CACHE.with(|cache_ref| {
                                Ok::<_, String>(cache_ref.borrow().get(&cache_key).unwrap().clone())
                            })?;
                            
                            for (i, (patterns, body)) in clauses.iter().enumerate() {
                                if let Some((body_env, subst_cost)) = crate::eval::forms::query::match_clause(patterns, &new_args, &base_env, funcs) {
                                    let clause = &cached[i];
                                    let body_cost = crate::eval::machine::budget::calculate_expr_cost(body);
                                    let total_cost = subst_cost + body_cost;
                                    
                                    let mut locals_to_push = Vec::with_capacity(clause.locals.len());
                                    for var in &clause.locals {
                                        let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                                        locals_to_push.push((val, Env::new()));
                                    }
                                    
                                    pending_calls.push(super::state::PendingCall {
                                        body_code: clause.body_code.clone(),
                                        free_vars: Arc::from(clause.free_vars.clone()),
                                        body_env,
                                        locals_to_push,
                                        cost: total_cost,
                                    });
                                }
                            }
                        }
                        
                        let frame = CallFrame {
                            return_ip: state.ip,
                            return_code: state.code.clone(),
                            locals_to_pop: 0,
                            saved_base_env: base_env.clone(),
                            saved_locals: Vec::new(),
                            saved_free_vars_map: state.free_vars_map.clone(),
                            saved_free_vars_bindings: state.free_vars_bindings.clone(),
                            kind: CallFrameKind::Call {
                                name,
                                arity,
                                pending_calls,
                                next_idx: 0,
                                results: Vec::new(),
                                memo_key: None,
                            },
                        };
                        state.frames.push(frame);
                        if let Some(next_env) = run_next_call_iteration(&mut state, funcs)? {
                            base_env = next_env;
                        }
                        continue;
                    }
                }

                let mut found_call = false;
                while let Some(frame) = state.frames.last() {
                    if matches!(frame.kind, CallFrameKind::Call { .. }) {
                        found_call = true;
                        break;
                    }
                    state.frames.pop();
                }
                
                if found_call {
                    // State at this point:
                    // - Compiler emitted Store(0..arity-1) with new args BEFORE TailCallSelf
                    // - So state.locals[0..arity-1] contain the new args
                    // - Let* bindings occupy higher indices (state.locals[arity..])
                    // - The CallFrame has saved_locals = parent's locals
                    
                    // Get arity from the CallFrame
                    let arity = if let Some(frame) = state.frames.last() {
                        if let CallFrameKind::Call { arity, .. } = &frame.kind {
                            *arity
                        } else { unreachable!() }
                    } else { unreachable!() };
                    
                    // Save the new args before restoring parent's locals
                    let new_args: Vec<Atom> = state.locals.iter().take(arity as usize).map(|(atom, _)| atom.clone()).collect();
                    
                    // Pop the CallFrame to get saved_locals (parent's locals)
                    let mut frame = state.frames.pop().unwrap();
                    
                    // Restore parent's locals
                    state.locals = std::mem::take(&mut frame.saved_locals);
                    
                    let name = if let CallFrameKind::Call { name, .. } = &frame.kind {
                        *name
                    } else { unreachable!() };
                    
                    let mut pending_calls = Vec::new();
                    if let Some(clauses) = crate::eval::forms::query::lookup_user_clauses(name, arity, funcs) {
                        let cache_key = (name.to_string(), arity);
                        let cached = FN_BYTECODE_CACHE.with(|cache_ref| {
                            Ok::<_, String>(cache_ref.borrow().get(&cache_key).unwrap().clone())
                        })?;
                        
                        for (i, (patterns, body)) in clauses.iter().enumerate() {
                            if let Some((body_env, subst_cost)) = crate::eval::forms::query::match_clause(patterns, &new_args, &base_env, funcs) {
                                let clause = &cached[i];
                                let body_cost = crate::eval::machine::budget::calculate_expr_cost(body);
                                let total_cost = subst_cost + body_cost;
                                
                                let mut locals_to_push = Vec::with_capacity(clause.locals.len());
                                for var in &clause.locals {
                                    let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                                    locals_to_push.push((val, Env::new()));
                                }
                                
                                pending_calls.push(super::state::PendingCall {
                                    body_code: clause.body_code.clone(),
                                    free_vars: Arc::from(clause.free_vars.clone()),
                                    body_env,
                                    locals_to_push,
                                    cost: total_cost,
                                });
                            }
                        }
                    }
                    
                    // Replace frame's state: new pending calls, cleared results, empty saved_locals
                    if let CallFrameKind::Call { pending_calls: old_pending, next_idx, .. } = &mut frame.kind {
                        *old_pending = pending_calls;
                        *next_idx = 0;
                    }
                    frame.locals_to_pop = 0;
                    
                    state.frames.push(frame);
                    if let Some(next_env) = run_next_call_iteration(&mut state, funcs)? {
                        base_env = next_env;
                    }
                    continue;
                } else {
                    return Ok((plain(Vec::new()), state.budget, VmExit::TailCall(state.locals)));
                }
            }
        }
    }
        
    if state.ip >= state.code.len() || state.cut_executed {
            if let Some(frame) = state.frames.last_mut() {
                let sub_results = state.stack.pop().unwrap_or_else(|| Vec::new());
                
                // For Call and Eval frames, restore parent's locals from saved_locals (replaces extend).
                // For other frames, truncate by locals_to_pop as before.
                // restore parent's locals for Eval frames too
                if matches!(frame.kind, CallFrameKind::Call { .. } | CallFrameKind::Eval { .. }) {
                    state.locals = frame.saved_locals.clone();
                } else {
                    let new_len = state.locals.len().saturating_sub(frame.locals_to_pop);
                    state.locals.truncate(new_len);
                    frame.locals_to_pop = 0;
                }
                
                match &mut frame.kind {
                    CallFrameKind::Let { results, .. } => { results.extend(sub_results); }
                    CallFrameKind::If { results, .. } => { results.extend(sub_results); }
                    CallFrameKind::Case { results, .. } => { results.extend(sub_results); }
                    CallFrameKind::Call { results, .. } => {
                        let merged: Vec<(Atom, Env)> = sub_results
                            .into_iter()
                            .map(|(atom, env)| {
                                let merged_env = crate::eval::shared::env::prepend_chain(env, &base_env);
                                (atom, merged_env)
                            })
                            .collect();
                        results.extend(merged);
                    }
                    CallFrameKind::Eval { results, .. } => { results.extend(sub_results); }
                    CallFrameKind::Normal => { state.stack.push(sub_results); }
                }
                
                let force_finish = state.cut_executed;
                let restored_env = frame.saved_base_env.clone();
                
                if force_finish {
                    let popped = state.frames.pop().unwrap();
                    state.code = popped.return_code;
                    state.ip = popped.return_ip + 1;
                    state.free_vars_map = popped.saved_free_vars_map;
                    state.free_vars_bindings = popped.saved_free_vars_bindings;
                    
                    match popped.kind {
                        CallFrameKind::Let { results, .. } => { state.stack.push(results); }
                        CallFrameKind::If { results, .. } => {
                            state.stack.push(results);
                        }
                        CallFrameKind::Case { results, .. } => { state.stack.push(results); }
                        CallFrameKind::Call { results, .. }
                        | CallFrameKind::Eval { results, .. } => {
                            // restore parent's locals for Eval as well
                            state.locals = popped.saved_locals;
                            state.stack.push(results);
                        }
                        CallFrameKind::Normal => {}
                    }
                    base_env = restored_env;
                } else {
                    match &frame.kind {
                        CallFrameKind::Let { .. } => {
                            if let Some(next_env) = run_next_let_iteration(&mut state, funcs)? {
                                base_env = next_env;
                            } else {
                                base_env = restored_env;
                            }
                        }
                        CallFrameKind::If { .. } => {
                            if let Some(next_env) = run_next_if_iteration(&mut state)? {
                                base_env = next_env;
                            } else {
                                base_env = restored_env;
                            }
                        }
                        CallFrameKind::Case { .. } => {
                            if let Some(next_env) = run_next_case_iteration(&mut state, funcs)? {
                                base_env = next_env;
                            } else {
                                base_env = restored_env;
                            }
                        }
                        CallFrameKind::Call { .. } => {
                            if let Some(next_env) = run_next_call_iteration(&mut state, funcs)? {
                                base_env = next_env;
                            } else {
                                base_env = restored_env;
                            }
                        }
                        CallFrameKind::Eval { .. } => {
                            if let Some(next_env) = run_next_eval_iteration(&mut state, funcs)? {
                                base_env = next_env;
                            } else {
                                base_env = restored_env;
                            }
                        }
                        CallFrameKind::Normal => {
                            let popped = state.frames.pop().unwrap();
                            state.code = popped.return_code;
                            state.ip = popped.return_ip + 1;
                            state.free_vars_map = popped.saved_free_vars_map;
                            state.free_vars_bindings = popped.saved_free_vars_bindings;
                            base_env = restored_env;
                        }
                    }
                }
                continue;
            } else {
                break;
            }
        }
    }

    let final_rs = state.stack.pop().unwrap_or_else(|| plain(Vec::new()));
    let prepended_rs: Vec<(Atom, Env)> = final_rs
        .into_iter()
        .map(|(atom, env)| {
            let merged = crate::eval::shared::env::prepend_chain(env, &base_env);
            (atom, merged)
        })
        .collect();
    let exit = if state.cut_executed { VmExit::Cut } else { VmExit::Normal };
    Ok((prepended_rs, state.budget, exit))
}

fn collect_pattern_vars(expr: &Expr, set: &mut Vec<String>) {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            if !set.contains(s) {
                set.push(s.clone());
            }
        }
        Expr::List(items) => {
            for item in items.iter() {
                collect_pattern_vars(item, set);
            }
        }
        _ => {}
    }
}

fn eval_call_vm(
    head: Expr,
    args: Vec<Expr>,
    env: &Env,
    funcs: &FnTable,
    budget: &mut Option<i64>,
    free_vars_map: &[String],
    free_vars_bindings: &[Atom],
) -> Result<ResultSet, String> {
    let call = Expr::List(Arc::from(
        std::iter::once(head).chain(args.into_iter()).collect::<Vec<_>>()
    ));
    let mut comp = super::compiler::VMCompiler::new(&[], None);
    let mut code = Vec::new();
    if comp.compile(&call, &mut code, false).is_ok() {
        let sub_state = VMState::new_with_parent(
            std::sync::Arc::from(code),
            std::sync::Arc::from(comp.free_vars.clone()),
            *budget,
            free_vars_map,
            free_vars_bindings,
        );
        let mut sub_env = env.clone();
        for (i, name) in comp.free_vars.iter().enumerate() {
            if let Some(val) = env.get(name) {
                if let Atom::Sym(fresh_name) = &sub_state.free_vars_bindings[i] {
                    sub_env = sub_env.extend(fresh_name, val.clone());
                }
            }
        }
        let (res, sub_budget, _) = run_vm(sub_state, funcs, &sub_env)?;
        *budget = sub_budget;
        Ok(res)
    } else {
        crate::eval::machine::step::run_rs(Arc::new(call), env.clone(), funcs, budget)
    }
}

fn dispatch_call(
    head_atom: &Atom,
    args: &[Atom],
    arity: u8,
    combo_env: &Env,
    funcs: &FnTable,
    results: &mut Vec<(Atom, Env)>,
    pending_calls: &mut Vec<super::state::PendingCall>,
    memo_key_out: &mut Option<(String, Vec<Atom>)>,
) -> Result<(), String> {
    // recursively resolve and evaluate function calls and partial applications (currying)
    match head_atom {
        Atom::Sym(fn_name) => {
            if let Some(function) = funcs.get(fn_name, arity) {
                match &function.kind {
                    FunctionKind::Native { func: native_f } => {
                        let _profile = if cfg!(feature = "profile") {
                            Some(crate::profile::ProfileGuard::new_owned(fn_name))
                        } else {
                            None
                        };
                        // special case for "member" to bind input variables in the environment
                        if fn_name.as_ref() == "member" && arity == 2 {
                            if let Atom::Sym(ref s) = args[1] {
                                if s.starts_with('$') && combo_env.get(s).is_none() {
                                    let id = crate::eval::machine::vm::state::next_fresh_id();
                                    let fresh_tail = format!("$__fresh_tail_{}", id);
                                    let list_val = Atom::Expr(crate::atom::expr_data(vec![args[0].clone(), Atom::sym(&fresh_tail)]));
                                    let mut merged_env = combo_env.clone();
                                    merged_env = crate::eval::shared::env::bind(&merged_env, s, list_val);
                                    results.push((Atom::sym("True"), merged_env));
                                    return Ok(());
                                }
                            }
                            let items = match &args[1] {
                                Atom::Expr(v) => v.to_vec(),
                                other => vec![other.clone()],
                            };
                            for item in &items {
                                if args[0] == *item {
                                    results.push((Atom::sym("True"), combo_env.clone()));
                                } else if let Some(bindings) = crate::eval::machine::state::unify(&args[0], item) {
                                    let mut merged_env = combo_env.clone();
                                    for (name, val) in bindings {
                                        merged_env = crate::eval::shared::env::bind(&merged_env, &name, val);
                                    }
                                    results.push((Atom::sym("True"), merged_env));
                                }
                            }
                            return Ok(());
                        }
                        // special case for "is-member" to bind input variables in the environment
                        if fn_name.as_ref() == "is-member" && arity == 2 {
                            if let Atom::Sym(ref s) = args[1] {
                                if s.starts_with('$') && combo_env.get(s).is_none() {
                                    let id = crate::eval::machine::vm::state::next_fresh_id();
                                    let fresh_tail = format!("$__fresh_tail_{}", id);
                                    let list_val = Atom::Expr(crate::atom::expr_data(vec![args[0].clone(), Atom::sym(&fresh_tail)]));
                                    let mut merged_env = combo_env.clone();
                                    merged_env = crate::eval::shared::env::bind(&merged_env, s, list_val);
                                    results.push((crate::builtins::boolean::bool_atom(true), merged_env));
                                    return Ok(());
                                }
                            }
                            let items = match &args[1] {
                                Atom::Expr(v) => v.to_vec(),
                                other => vec![other.clone()],
                            };
                            let mut unifiable_results = Vec::new();
                            for item in &items {
                                if args[0] == *item {
                                    unifiable_results.push((crate::builtins::boolean::bool_atom(true), combo_env.clone()));
                                } else if let Some(bindings) = crate::eval::machine::state::unify(&args[0], item) {
                                    let mut merged_env = combo_env.clone();
                                    for (name, val) in bindings {
                                        merged_env = crate::eval::shared::env::bind(&merged_env, &name, val);
                                    }
                                    unifiable_results.push((crate::builtins::boolean::bool_atom(true), merged_env));
                                }
                            }
                            if unifiable_results.is_empty() {
                                results.push((crate::builtins::boolean::bool_atom(false), combo_env.clone()));
                            } else {
                                results.extend(unifiable_results);
                            }
                            return Ok(());
                        }
                        let res = native_f(args, funcs)?;
                        for a in res {
                            results.push((a, combo_env.clone()));
                        }
                        return Ok(());
                    }
                }
            }

            // retrieve cached result if user function is pure and already computed
            if funcs.is_pure_fn(fn_name, arity) {
                let k = (fn_name.to_string(), args.to_vec());
                if let Some(cached) = funcs.memo_get(&k) {
                    results.extend(cached.into_iter().map(|a| (a, combo_env.clone())));
                    return Ok(());
                }
                *memo_key_out = Some(k);
            }

            let mut matched_any = false;
            let user_clauses = crate::eval::forms::query::lookup_user_clauses(fn_name, arity, funcs);
            let has_clauses = user_clauses.is_some();
            if let Some(clauses) = user_clauses {
                let cache_key = (fn_name.to_string(), arity);
                let cached = FN_BYTECODE_CACHE.with(|cache_ref| {
                    let mut cache = cache_ref.borrow_mut();
                    if let Some(entry) = cache.get(&cache_key) {
                        return Ok::<_, String>(entry.clone());
                    }
                    let mut compiled = Vec::with_capacity(clauses.len());
                    for (pat, b) in &clauses {
                        let mut comp = super::compiler::VMCompiler::new(pat, Some(fn_name.to_string()));
                        let mut code = Vec::new();
                        comp.compile(b, &mut code, true)?;
                        compiled.push(CompiledClause {
                            body_code: std::sync::Arc::from(code),
                            free_vars: comp.free_vars,
                            locals: comp.locals,
                        });
                    }
                    cache.insert(cache_key, compiled.clone());
                    Ok(compiled)
                })?;

                for (i, (patterns, body)) in clauses.iter().enumerate() {
                    if let Some((body_env, subst_cost)) = crate::eval::forms::query::match_clause(patterns, args, combo_env, funcs) {
                        matched_any = true;
                        let clause = &cached[i];
                        let body_cost = crate::eval::machine::budget::calculate_expr_cost(body);
                        let total_cost = subst_cost + body_cost;

                        let mut locals_to_push = Vec::with_capacity(clause.locals.len());
                        for var in &clause.locals {
                            let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                            locals_to_push.push((val, Env::new()));
                        }

                        pending_calls.push(super::state::PendingCall {
                            body_code: clause.body_code.clone(),
                            free_vars: Arc::from(clause.free_vars.clone()),
                            body_env,
                            locals_to_push,
                            cost: total_cost,
                        });
                    }
                }
            }

            if !matched_any {
                if funcs.has_greater_arity(fn_name, arity) {
                    let partial_atom = Atom::Expr(crate::atom::expr_data(vec![
                        Atom::sym("partial"),
                        head_atom.clone(),
                        Atom::Expr(crate::atom::expr_data(args.to_vec())),
                    ]));
                    results.push((partial_atom, combo_env.clone()));
                } else if has_clauses {
                    // defined user function with no matching clauses under PeTTa semantics returns empty/fails
                } else {
                    let mut items = vec![Atom::sym(fn_name)];
                    items.extend(args.to_vec());
                    let substituted: Vec<Atom> = items
                        .iter()
                        .map(|a| crate::eval::shared::subst::subst_atom(a, combo_env))
                        .collect();
                    results.push((Atom::Expr(crate::atom::expr_data(substituted)), combo_env.clone()));
                }
            }
        }
        Atom::Closure(c) => {
            let mut matched_any = false;
            let clauses: Vec<(Vec<Expr>, Expr)> = vec![(c.params.clone(), c.body.clone())];
            for (patterns, body) in &clauses {
                if let Some((body_env, _subst_cost)) = crate::eval::forms::query::match_clause(patterns, args, combo_env, funcs) {
                    matched_any = true;
                    let body_renamed = crate::eval::shared::fresh::rename_apart_unbound_vars(
                        body,
                        patterns,
                    );
                    let mut comp = super::compiler::VMCompiler::new(patterns, None);
                    let mut code = Vec::new();
                    comp.compile(&body_renamed, &mut code, false)?;

                    let mut locals_to_push = Vec::with_capacity(comp.locals.len());
                    for var in &comp.locals {
                        let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                        locals_to_push.push((val, Env::new()));
                    }

                    pending_calls.push(super::state::PendingCall {
                        body_code: std::sync::Arc::from(code),
                        free_vars: Arc::from(comp.free_vars),
                        body_env,
                        locals_to_push,
                        cost: 0,
                    });
                }
            }
            if !matched_any {
                let params_len = c.params.len();
                if (arity as usize) < params_len {
                    let partial_atom = Atom::Expr(crate::atom::expr_data(vec![
                        Atom::sym("partial"),
                        head_atom.clone(),
                        Atom::Expr(crate::atom::expr_data(args.to_vec())),
                    ]));
                    results.push((partial_atom, combo_env.clone()));
                } else {
                    let mut items = vec![head_atom.clone()];
                    items.extend(args.to_vec());
                    let substituted: Vec<Atom> = items
                        .iter()
                        .map(|a| crate::eval::shared::subst::subst_atom(a, combo_env))
                        .collect();
                    results.push((Atom::Expr(crate::atom::expr_data(substituted)), combo_env.clone()));
                }
            }
        }
        Atom::Expr(parts) if parts.len() == 3 && parts[0] == Atom::sym("partial") => {
            let inner_head = &parts[1];
            let old_args: Vec<Atom> = match &parts[2] {
                Atom::Expr(v) => v.to_vec(),
                other => vec![other.clone()],
            };
            let mut combined_args = old_args;
            combined_args.extend(args.to_vec());
            let combined_arity = combined_args.len() as u8;
            dispatch_call(
                inner_head,
                &combined_args,
                combined_arity,
                combo_env,
                funcs,
                results,
                pending_calls,
                memo_key_out,
            )?;
        }
        _ => {
            let mut items = vec![head_atom.clone()];
            items.extend(args.to_vec());
            let substituted: Vec<Atom> = items
                .iter()
                .map(|a| crate::eval::shared::subst::subst_atom(a, combo_env))
                .collect();
            results.push((Atom::Expr(crate::atom::expr_data(substituted)), combo_env.clone()));
        }
    }
    Ok(())
}

/// Run the next iteration of the Let opcode in flat frame-based control flow.
fn run_next_let_iteration(state: &mut VMState, funcs: &FnTable) -> Result<Option<Env>, String> {
    let mut to_run = None;
    if let Some(frame) = state.frames.last_mut() {
        if let CallFrameKind::Let {
            value_rs,
            next_idx,
            pattern,
            pattern_vars,
            free_vars_map,
            body_code,
            results: _,
        } = &mut frame.kind {
            while *next_idx < value_rs.len() {
                let (value, value_env) = &value_rs[*next_idx];
                *next_idx += 1;
                if let Some(match_env) = crate::eval::shared::pattern::try_match_one(
                    pattern,
                    value,
                    &Env::new(),
                    funcs,
                )? {
                    let body_env = crate::eval::shared::env::prepend_chain(match_env, value_env);
                    let mut locals_to_push = Vec::new();
                    for var in pattern_vars {
                        let bound = body_env.get(var).unwrap_or(Atom::sym("()"));
                        locals_to_push.push((bound, Env::new()));
                    }
                    frame.locals_to_pop = locals_to_push.len();
                    to_run = Some((body_code.clone(), free_vars_map.clone(), body_env, locals_to_push));
                    break;
                } else {
                    crate::eval::shared::debug::logical_failure(|| {
                        format!(
                            "warn: let pattern {} does not match value {}",
                            pattern.to_string(),
                            value.to_sexpr_string(),
                        )
                    });
                }
            }
        }
    }
    
    if let Some((body_code, free_vars_map, body_env, locals_to_push)) = to_run {
        // propagate let value bindings to existing local variables
        for (val, env) in &mut state.locals {
            let substituted = crate::eval::shared::subst::subst_atom(val, &body_env);
            *val = substituted;
            *env = crate::eval::shared::env::prepend_chain(body_env.clone(), env);
        }
        state.locals.extend(locals_to_push);
        state.code = body_code;
        state.ip = 0;
        
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                    state.free_vars_bindings[pos].clone()
                } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = super::state::next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();
        state.free_vars_map = free_vars_map;
        state.free_vars_bindings = free_vars_bindings;
        Ok(Some(body_env))
    } else {
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::Let { results, .. } = frame.kind {
            state.code = frame.return_code;
            state.ip = frame.return_ip + 1;
            state.free_vars_map = frame.saved_free_vars_map;
            state.free_vars_bindings = frame.saved_free_vars_bindings;
            state.stack.push(results);
            Ok(None)
        } else {
            unreachable!()
        }
    }
}

/// Run the next iteration of the If opcode in flat frame-based control flow.
fn run_next_if_iteration(state: &mut VMState) -> Result<Option<Env>, String> {
    // cond_env passed alongside branch_env so free-variable bindings
    // from the condition (e.g. $M bound by a called function) propagate into
    // the branch code's free_vars_bindings. Without this, LoadFree gets the
    // stale fresh-variable name instead of the value myf produced.
    let mut to_run: Option<(Arc<[Opcode]>, Arc<[String]>, Env, Option<Env>)> = None;
    if let Some(frame) = state.frames.last_mut() {
        if let CallFrameKind::If {
            condition_rs,
            next_idx,
            then_code,
            else_code,
            free_vars_map,
            results: _,
        } = &mut frame.kind {
            while *next_idx < condition_rs.len() {
                let (cond, cond_env) = &condition_rs[*next_idx];
                *next_idx += 1;
                
                let is_true = match cond {
                    Atom::Sym(s) => s.as_ref().eq_ignore_ascii_case("true"),
                    _ => false,
                };
                
                if is_true {
                    let branch_env = crate::eval::shared::pattern::prepend_env(cond_env.clone(), &frame.saved_base_env);
                    to_run = Some((then_code.clone(), free_vars_map.clone(), branch_env, Some(cond_env.clone())));
                    break;
                } else {
                    to_run = Some((else_code.clone(), free_vars_map.clone(), frame.saved_base_env.clone(), None));
                    break;
                }
            }
        }
    }
    
    if let Some((code_to_run, free_vars_map, branch_env, cond_env_opt)) = to_run {
        // propagate condition bindings to existing local variables
        if let Some(ref cond_env) = cond_env_opt {
            for (val, env) in &mut state.locals {
                let substituted = crate::eval::shared::subst::subst_atom(val, cond_env);
                *val = substituted;
                *env = crate::eval::shared::env::prepend_chain(cond_env.clone(), env);
            }
        }
        state.code = code_to_run;
        state.ip = 0;
        
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                // resolve free vars from cond_env first so bindings
                // created during condition evaluation propagate to branch code
                if let Some(ref cond_env) = cond_env_opt {
                    if let Some(atom) = cond_env.get(name) {
                        return atom;
                    }
                }
                if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                    state.free_vars_bindings[pos].clone()
                } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = super::state::next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();
        state.free_vars_map = free_vars_map;
        state.free_vars_bindings = free_vars_bindings;
        Ok(Some(branch_env))
    } else {
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::If {
            results,
            ..
        } = frame.kind {
            state.code = frame.return_code;
            state.ip = frame.return_ip + 1;
            state.free_vars_map = frame.saved_free_vars_map;
            state.free_vars_bindings = frame.saved_free_vars_bindings;
            
            state.stack.push(results);
            Ok(None)
        } else {
            unreachable!()
        }
    }
}

/// Run the next iteration of the Case opcode in flat frame-based control flow.
fn run_next_case_iteration(state: &mut VMState, funcs: &FnTable) -> Result<Option<Env>, String> {
    let mut to_run = None;
    if let Some(frame) = state.frames.last_mut() {
        if let CallFrameKind::Case {
            scrutinee_rs,
            next_idx,
            branches,
            results: _,
        } = &mut frame.kind {
            if scrutinee_rs.is_empty() {
                if *next_idx == 0 {
                    *next_idx = 1;
                    for branch in branches {
                        if matches!(&branch.pattern, Expr::Symbol(s) if s == "Empty") {
                            to_run = Some((branch.body_code.clone(), branch.free_vars_map.clone(), frame.saved_base_env.clone(), Vec::new()));
                            break;
                        }
                    }
                }
            } else {
                while *next_idx < scrutinee_rs.len() {
                    let (value, value_env) = &scrutinee_rs[*next_idx];
                    *next_idx += 1;
                    
                    let mut selected = None;
                    for branch in branches {
                        if matches!(&branch.pattern, Expr::Symbol(s) if s == "Empty") {
                            continue;
                        }
                        if matches!(&branch.pattern, Expr::Symbol(s) if s == "$else") {
                            selected = Some((branch, value_env.clone()));
                            break;
                        }
                        if let Some(match_env) = crate::eval::shared::pattern::try_match_one(
                            &branch.pattern,
                            value,
                            &Env::new(),
                            funcs,
                        )? {
                            let body_env = crate::eval::shared::env::prepend_chain(match_env, value_env);
                            selected = Some((branch, body_env));
                            break;
                        }
                    }
                    
                    if let Some((branch, body_env)) = selected {
                        let mut locals_to_push = Vec::new();
                        for var in &branch.pattern_vars {
                            let bound = body_env.get(var).unwrap_or(Atom::sym("()"));
                            locals_to_push.push((bound, Env::new()));
                        }
                        frame.locals_to_pop = locals_to_push.len();
                        to_run = Some((branch.body_code.clone(), branch.free_vars_map.clone(), body_env, locals_to_push));
                        break;
                    } else {
                        return Err(format!(
                            "case: no clause matched value {}",
                            value.to_sexpr_string()
                        ));
                    }
                }
            }
        }
    }
    
    if let Some((body_code, free_vars_map, body_env, locals_to_push)) = to_run {
        // propagate case scrutinee/match bindings to existing local variables
        for (val, env) in &mut state.locals {
            let substituted = crate::eval::shared::subst::subst_atom(val, &body_env);
            *val = substituted;
            *env = crate::eval::shared::env::prepend_chain(body_env.clone(), env);
        }
        state.locals.extend(locals_to_push);
        state.code = body_code;
        state.ip = 0;
        
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                    state.free_vars_bindings[pos].clone()
                } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = super::state::next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();
        state.free_vars_map = free_vars_map;
        state.free_vars_bindings = free_vars_bindings;
        Ok(Some(body_env))
    } else {
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::Case { results, .. } = frame.kind {
            state.code = frame.return_code;
            state.ip = frame.return_ip + 1;
            state.free_vars_map = frame.saved_free_vars_map;
            state.free_vars_bindings = frame.saved_free_vars_bindings;
            state.stack.push(results);
            Ok(None)
        } else {
            unreachable!()
        }
    }
}

/// Run the next iteration of the Call opcode in flat frame-based control flow.
fn run_next_call_iteration(state: &mut VMState, funcs: &FnTable) -> Result<Option<Env>, String> {
    let mut to_run = None;
    if let Some(frame) = state.frames.last_mut() {
        if let CallFrameKind::Call {
            pending_calls,
            next_idx,
            ..
        } = &mut frame.kind {
            if *next_idx < pending_calls.len() {
                let pending = &pending_calls[*next_idx];
                *next_idx += 1;
                
                if let Some(b) = state.budget {
                    if b <= pending.cost {
                        return Err("Budget exhausted".into());
                    }
                    state.budget = Some(b - pending.cost);
                }
                
                to_run = Some((pending.body_code.clone(), pending.free_vars.clone(), pending.body_env.clone(), pending.locals_to_push.clone()));
            }
        }
    }
    
    if let Some((body_code, free_vars_map, body_env, locals_to_push)) = to_run {
        // Save parent's locals before entering function body, replace with callee's params.
        // This prevents absolute-index corruption (Load(0) seeing parent's param, not callee's).
        if let Some(frame) = state.frames.last_mut() {
            let parent_locals = std::mem::take(&mut state.locals);
            frame.saved_locals = parent_locals;
        }
        state.locals = locals_to_push;
        state.code = body_code;
        state.ip = 0;
        
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                    state.free_vars_bindings[pos].clone()
                } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = super::state::next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();
        state.free_vars_map = free_vars_map;
        state.free_vars_bindings = free_vars_bindings;
        Ok(Some(body_env))
    } else {
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::Call { results, memo_key, .. } = frame.kind {
            if let Some(key) = memo_key {
                // substitute environments on memoization results
                let atoms_only: Vec<Atom> = results.iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(a, env)).collect();
                funcs.memo_set(key, atoms_only);
            }
            state.code = frame.return_code;
            state.ip = frame.return_ip + 1;
            state.locals = frame.saved_locals;
            state.free_vars_map = frame.saved_free_vars_map;
            state.free_vars_bindings = frame.saved_free_vars_bindings;
            state.stack.push(results);
            Ok(None)
        } else {
            unreachable!()
        }
    }
}

/// Run the next iteration of the Eval opcode in flat frame-based control flow.
fn run_next_eval_iteration(state: &mut VMState, funcs: &FnTable) -> Result<Option<Env>, String> {
    let mut to_run: Option<(Arc<[Opcode]>, Arc<[String]>, Env)> = None;
    if let Some(frame) = state.frames.last_mut() {
        if let CallFrameKind::Eval {
            target_rs,
            next_idx,
            results,
        } = &mut frame.kind {
            while *next_idx < target_rs.len() {
                let (target_expr, target_env) = &target_rs[*next_idx];
                *next_idx += 1;
                
                let mut comp = super::compiler::VMCompiler::new(&[], None);
                let mut code = Vec::new();
                if comp.compile(target_expr, &mut code, false).is_ok() {
                    to_run = Some((std::sync::Arc::from(code), Arc::from(comp.free_vars), target_env.clone()));
                    break;
                } else {
                    let mut budget = state.budget;
                    let res = super::super::step::run_rs(Arc::new(target_expr.clone()), target_env.clone(), funcs, &mut budget)?;
                    state.budget = budget;
                    results.extend(res);
                }
            }
        }
    }
    
    if let Some((body_code, free_vars_map, body_env)) = to_run {
        // Save parent's locals before entering dynamic eval body, clear state.locals.
        // prevent Load(0) index contamination by isolating eval locals.
        if let Some(frame) = state.frames.last_mut() {
            let parent_locals = std::mem::take(&mut state.locals);
            frame.saved_locals = parent_locals;
        }
        state.locals = Vec::new();
        state.code = body_code;
        state.ip = 0;
        
        let free_vars_bindings = free_vars_map
            .iter()
            .map(|name| {
                if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                    state.free_vars_bindings[pos].clone()
                } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                    Atom::sym(name)
                } else {
                    let id = super::state::next_fresh_id();
                    let hint = name.strip_prefix('$').unwrap_or(name);
                    let fresh_name = format!("$__fresh_{hint}_{id}");
                    Atom::sym(&fresh_name)
                }
            })
            .collect();
        state.free_vars_map = free_vars_map;
        state.free_vars_bindings = free_vars_bindings;
        Ok(Some(body_env))
    } else {
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::Eval { results, .. } = frame.kind {
            state.code = frame.return_code;
            state.ip = frame.return_ip + 1;
            state.locals = frame.saved_locals; // restore parent's locals
            state.free_vars_map = frame.saved_free_vars_map;
            state.free_vars_bindings = frame.saved_free_vars_bindings;
            state.stack.push(results);
            Ok(None)
        } else {
            unreachable!()
        }
    }
}
