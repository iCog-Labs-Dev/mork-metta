use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use crate::func::{FnTable, FunctionKind};
use crate::eval::machine::budget::{ResultSet, plain};
use rayon::prelude::*;
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

/// Trampoline entry point. Runs the VM without ever growing the C stack;
/// all sub-VM calls are dispatched through a heap-allocated call stack.
pub fn run_vm(
    initial_state: VMState,
    funcs: &FnTable,
    initial_base_env: &Env,
) -> Result<(ResultSet, Option<i64>, VmExit), String> {
    super::compiler::set_current_funcs(funcs);
    let _guard = VmDepthGuard::enter();

    // Each entry is a suspended parent frame waiting for a sub-VM result.
    // We push (parent, parent_env) when yielding, then pop when the sub finishes.
    let mut call_stack: Vec<(Box<VMState>, Env)> = Vec::new();
    let mut current_state = Box::new(initial_state);
    let mut current_env  = initial_base_env.clone();

    loop {
        match run_vm_inner(*current_state, funcs, &current_env)? {
            (res, budget, VmExit::YieldCall { parent_state, parent_env, sub_state, sub_env }) => {
                // The inner loop yielded: push the suspended parent and descend into the sub-VM.
                call_stack.push((parent_state, parent_env));
                current_state = sub_state;
                current_env   = sub_env;
                // (budget already propagated into parent_state by the yield macro)
                let _ = budget;
            }
            (res, budget, terminal_exit) => {
                // A VM finished normally (Normal/Cut/TailCall).
                if let Some((mut parent, parent_env)) = call_stack.pop() {
                    // Deliver result to parent's last_sub_result, re-run the same opcode.
                    parent.budget = budget;
                    parent.last_sub_result = Some((res, terminal_exit));
                    current_state = parent;
                    current_env   = parent_env;
                } else {
                    // Stack empty — this is the final result.
                    return Ok((res, budget, terminal_exit));
                }
            }
        }
    }
}

/// Inner VM interpreter. Never calls itself recursively. Uses `yield_vm!`
/// to suspend and hand control back to the trampoline in `run_vm`.
fn run_vm_inner(
    mut state: VMState,
    funcs: &FnTable,
    initial_base_env: &Env,
) -> Result<(ResultSet, Option<i64>, VmExit), String> {
    // Suspend this VM: save state, hand sub-VM to trampoline.
    // On next invocation the same opcode checks state.last_sub_result.
    macro_rules! yield_vm {
        ($state:expr, $sub_state:expr, $sub_env:expr) => {
            return Ok((
                Vec::new(),
                $state.budget,
                VmExit::YieldCall {
                    parent_env:   initial_base_env.clone(),
                    parent_state: Box::new($state),
                    sub_state:    Box::new($sub_state),
                    sub_env:      $sub_env,
                },
            ))
        };
    }


    let mut base_env = initial_base_env.clone();
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
                enum UnifyIter {
                    Space(std::vec::IntoIter<crate::space::MatchResult>),
                    Vals(std::vec::IntoIter<(Atom, Env)>, Option<Atom>),
                    None,
                }

                struct UnifyResume {
                    results: Vec<(crate::atom::Atom, Env)>,
                    iter: UnifyIter,
                    current_env: Env,
                    precomputed_bindings: Vec<Atom>,
                    matched_any: bool,
                    emit_else: bool,
                }

                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<UnifyResume>().ok()) {
                    Some(mut r) => {
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            r.results.extend(sub_res);
                            match sub_exit {
                                VmExit::Cut => { state.cut_executed = true; r.iter = UnifyIter::None; r.emit_else = false; }
                                VmExit::TailCall(locs) => {
                                    return Ok((r.results, state.budget, VmExit::TailCall(locs)));
                                }
                                VmExit::Normal => {}
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        *r
                    }
                    None => {
                        let val_b_rs = state.stack.pop().ok_or("VM stack underflow on Unify B")?;
                        let val_a_rs = state.stack.pop().ok_or("VM stack underflow on Unify A")?;

                        let mut current_env = base_env.clone();
                        for (i, name) in local_names.iter().enumerate() {
                            if let Some((val, _)) = state.locals.get(i) {
                                current_env = crate::eval::shared::env::prepend_chain(
                                    crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                                    &current_env,
                                );
                            }
                        }

                        let precomputed_bindings: Vec<Atom> = free_vars_map.iter().map(|name| {
                            if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                                state.free_vars_bindings[pos].clone()
                            } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                                Atom::sym(name)
                            } else {
                                let id = crate::eval::machine::vm::state::next_fresh_id();
                                let hint = name.strip_prefix('$').unwrap_or(name);
                                Atom::sym(&format!("$__fresh_{hint}_{id}"))
                            }
                        }).collect();

                        let first_a = val_a_rs.first().map(|(a, _)| a);
                        let is_space = matches!(first_a, Some(Atom::Sym(s)) if s.starts_with('&'));

                        let (iter, emit_else) = if is_space {
                            let space_ref = first_a.unwrap();
                            let matches = crate::space::query::collect_match_results(
                                funcs, space_ref, pattern_b, &current_env,
                            )?;
                            let empty = matches.is_empty();
                            (UnifyIter::Space(matches.into_iter()), empty)
                        } else {
                            let a_opt = val_a_rs.first().map(|(a, _)| a.clone());
                            (UnifyIter::Vals(val_b_rs.into_iter(), a_opt), false)
                        };

                        UnifyResume {
                            results: Vec::new(),
                            iter,
                            current_env,
                            precomputed_bindings,
                            matched_any: false,
                            emit_else,
                        }
                    }
                };

                let mut sub_state_opt = None;
                let mut sub_env_opt = None;

                if !state.cut_executed {
                    match &mut resume.iter {
                        UnifyIter::Space(iter) => {
                            if let Some(m) = iter.next() {
                                resume.matched_any = true;
                                let mut sub_locals = state.locals.clone();
                                for var in pattern_vars {
                                    let bound = m.bindings.iter()
                                        .find(|(k, _)| k.as_ref() == var.as_str())
                                        .map(|(_, v)| (**v).clone())
                                        .unwrap_or_else(|| Atom::sym("()"));
                                    sub_locals.push((bound, Env::new()));
                                }
                                let sub_env = crate::eval::shared::env::bind_all(&resume.current_env, &m.bindings);
                                
                                let sub_state = VMState {
                                    code: then_code.clone(), ip: 0,
                                    stack: Vec::new(), locals: sub_locals,
                                    free_vars_map: free_vars_map.clone(),
                                    free_vars_bindings: resume.precomputed_bindings.clone(),
                                    frames: Vec::new(), budget: state.budget,
                                    cut_executed: false, resume_data: None, last_sub_result: None,
                                };
                                sub_state_opt = Some(sub_state);
                                sub_env_opt = Some(sub_env);
                            } else if resume.emit_else {
                                resume.emit_else = false;
                                let mut sub_locals = state.locals.clone();
                                let sub_state = VMState {
                                    code: else_code.clone(), ip: 0,
                                    stack: Vec::new(), locals: sub_locals,
                                    free_vars_map: free_vars_map.clone(),
                                    free_vars_bindings: resume.precomputed_bindings.clone(),
                                    frames: Vec::new(), budget: state.budget,
                                    cut_executed: false, resume_data: None, last_sub_result: None,
                                };
                                sub_state_opt = Some(sub_state);
                                sub_env_opt = Some(resume.current_env.clone());
                            }
                        }
                        UnifyIter::Vals(iter, val_a_opt) => {
                            let mut found = false;
                            if let Some(val_a) = val_a_opt {
                                while let Some((val_b, env_b)) = iter.next() {
                                    let match_env = crate::eval::shared::pattern::prepend_env(env_b, &resume.current_env);
                                    if let Some(matched_env) = crate::eval::shared::pattern::try_match_one(pattern_a, &val_b, &match_env, funcs)? {
                                        resume.matched_any = true;
                                        found = true;
                                        let mut sub_locals = state.locals.clone();
                                        for var in pattern_vars {
                                            let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                                            sub_locals.push((bound, Env::new()));
                                        }
                                        let sub_state = VMState {
                                            code: then_code.clone(), ip: 0,
                                            stack: Vec::new(), locals: sub_locals,
                                            free_vars_map: free_vars_map.clone(),
                                            free_vars_bindings: resume.precomputed_bindings.clone(),
                                            frames: Vec::new(), budget: state.budget,
                                            cut_executed: false, resume_data: None, last_sub_result: None,
                                        };
                                        sub_state_opt = Some(sub_state);
                                        sub_env_opt = Some(matched_env);
                                        break;
                                    }
                                }
                            }
                            if !found && !resume.matched_any {
                                resume.matched_any = true;
                                let mut sub_state = VMState::new_with_parent(
                                    else_code.clone(), free_vars_map.clone(), state.budget,
                                    &state.free_vars_map, &state.free_vars_bindings,
                                );
                                sub_state.locals = state.locals.clone();
                                sub_state_opt = Some(sub_state);
                                sub_env_opt = Some(resume.current_env.clone());
                            }
                        }
                        UnifyIter::None => {}
                    }
                }

                if let Some(sub_state) = sub_state_opt {
                    let sub_env = sub_env_opt.unwrap();
                    state.resume_data = Some(Box::new(resume));
                    yield_vm!(state, sub_state, sub_env);
                } else {
                    state.stack.push(resume.results);
                    state.ip += 1;
                }
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
                            Some(Atom::Sym(s)) => s.as_str(),
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
                // Resume struct for Match loop over space query results.
                struct MatchResume {
                    results: Vec<(crate::atom::Atom, Env)>,
                    pending: Vec<(VMState, Env)>,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<MatchResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            r.results.extend(sub_res);
                            match sub_exit {
                                VmExit::Cut => { state.cut_executed = true; r.pending.clear(); }
                                VmExit::TailCall(locs) => return Ok((r.results, state.budget, VmExit::TailCall(locs))),
                                VmExit::Normal => {}
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        let space_rs = state.stack.pop().ok_or("VM stack underflow on Match space")?;
                        let mut results = Vec::new();
                        let mut pending: Vec<(VMState, Env)> = Vec::new();
                        if let Some((space_ref, _)) = space_rs.first() {
                            let mut match_env = Env::new();
                            for (name, val) in local_names.iter().zip(state.locals.iter()) {
                                match_env = match_env.extend(name, val.0.clone());
                            }
                            if let Ok(matches) = crate::space::query::collect_match_results(funcs, space_ref, pattern, &match_env) {
                                if !matches.is_empty() {
                                    let precomputed_bindings: Vec<Atom> = free_vars_map.iter().map(|name| {
                                        if let Some(pos) = state.free_vars_map.iter().position(|x| x == name) {
                                            state.free_vars_bindings[pos].clone()
                                        } else if crate::eval::shared::fresh::is_generated_var_name(name) {
                                            Atom::sym(name)
                                        } else {
                                            let id = crate::eval::machine::vm::state::next_fresh_id();
                                            let hint = name.strip_prefix('$').unwrap_or(name);
                                            Atom::sym(&format!("$__fresh_{hint}_{id}"))
                                        }
                                    }).collect();
                                    for matched in matches {
                                        let mut sub_locals = state.locals.clone();
                                        for var in pattern_vars {
                                            let bound = matched.bindings.iter()
                                                .find(|(k, _)| k.as_ref() == var.as_str())
                                                .map(|(_, v)| (**v).clone())
                                                .unwrap_or_else(|| {
                                                    if let Some(idx) = local_names.iter().position(|x| x == var) {
                                                        state.locals[idx].0.clone()
                                                    } else { Atom::sym("()") }
                                                });
                                            sub_locals.push((bound, Env::new()));
                                        }
                                        let sub_state = VMState {
                                            code: body_code.clone(), ip: 0,
                                            stack: Vec::new(), locals: sub_locals,
                                            free_vars_map: free_vars_map.clone(),
                                            free_vars_bindings: precomputed_bindings.clone(),
                                            frames: Vec::new(), budget: state.budget,
                                            cut_executed: false, resume_data: None, last_sub_result: None,
                                        };
                                        let sub_env = crate::eval::shared::env::bind_all(&match_env, &matched.bindings);
                                        pending.push((sub_state, sub_env));
                                    }
                                }
                            }
                        }
                        MatchResume { results, pending }
                    }
                };
                while !resume.pending.is_empty() && !state.cut_executed {
                    let (sub_state, sub_env) = resume.pending.swap_remove(0);
                    state.resume_data = Some(Box::new(resume));
                    yield_vm!(state, sub_state, sub_env);
                }
                state.stack.push(resume.results);
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
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("Forall"))
                } else { None };
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

                let is_forall_true = gen_values.into_par_iter().all(|val| {
                    let mut local_budget = state.budget;
                    let mut call_env = crate::eval::shared::env::bind(&base_env, "$__fv", val);
                    if let Atom::Closure(_) = &check_atom {
                        let check_env = crate::eval::shared::env::bind(&base_env, "$__check_fn", check_atom.clone());
                        call_env = crate::eval::shared::pattern::prepend_env(check_env, &call_env);
                    }
                    if let Ok(res) = eval_call_vm(
                        check_head.clone(),
                        vec![Expr::Symbol("$__fv".to_string())],
                        &call_env,
                        funcs,
                        &mut local_budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    ) {
                        let results: Vec<Atom> = res.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                        !results.is_empty() && results.iter().all(|a| crate::eval::forms::control::is_truthy(a))
                    } else {
                        false
                    }
                });
                
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
                // FoldlLambda: resumable loop over list elements.
                struct FoldlLambdaResume {
                    current_acc: Atom,
                    items: Vec<Atom>,
                    next_item_idx: usize,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<FoldlLambdaResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            r.current_acc = sub_res.into_iter().next()
                                .map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                                .unwrap_or(r.current_acc);
                            match sub_exit {
                                VmExit::Cut => { state.cut_executed = true; }
                                VmExit::TailCall(locs) => return Ok((plain(vec![r.current_acc]), state.budget, VmExit::TailCall(locs))),
                                VmExit::Normal => {}
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        let acc_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda acc")?;
                        let list_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda list")?;
                        let acc = acc_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env))
                            .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
                        let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                            Some(Atom::Expr(v)) => v.to_vec(),
                            Some(other) => vec![other],
                            None => return Err("foldl-atom: list arg produced no result".to_string()),
                        };
                        FoldlLambdaResume { current_acc: acc, items, next_item_idx: 0 }
                    }
                };
                while resume.next_item_idx < resume.items.len() && !state.cut_executed {
                    let elem = resume.items[resume.next_item_idx].clone();
                    resume.next_item_idx += 1;
                    let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    sub_state.locals = state.locals.clone();
                    let vals_to_bind = [resume.current_acc.clone(), elem];
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
                    state.resume_data = Some(Box::new(resume));
                    yield_vm!(state, sub_state, step_env);
                }
                state.stack.push(plain(vec![resume.current_acc]));
                state.ip += 1;
            }
            Opcode::MapAtomLambda {
                var_name,
                body_code,
                free_vars_map,
            } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("MapAtomLambda"))
                } else { None };
                
                let list_rs = state.stack.pop().ok_or("VM stack underflow on MapAtomLambda")?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("map-atom: list arg produced no result".to_string()),
                };
                
                let mapped: Result<Vec<Atom>, String> = items.into_par_iter().map(|elem| {
                    let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    sub_state.locals = state.locals.clone();
                    sub_state.locals.push((elem.clone(), Env::new()));
                    let sub_env = base_env.extend(&var_name, elem);
                    let (res, _, _) = super::run_vm(sub_state, funcs, &sub_env)?;
                    let first = res.into_iter().next();
                    if let Some((val, e)) = first {
                        Ok(crate::eval::shared::subst::subst_atom(&val, &e))
                    } else {
                        Ok(Atom::sym("()"))
                    }
                }).collect();
                
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(mapped?))]));
                state.ip += 1;
            }
            Opcode::FilterAtomLambda {
                var_name,
                body_code,
                free_vars_map,
            } => {
                let _profile = if cfg!(feature = "profile") {
                    Some(crate::profile::ProfileGuard::new_owned("FilterAtomLambda"))
                } else { None };
                
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FilterAtomLambda")?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                    Some(Atom::Expr(v)) => v.to_vec(),
                    Some(other) => vec![other],
                    None => return Err("filter-atom: list arg produced no result".to_string()),
                };
                
                let mapped: Result<Vec<Option<Atom>>, String> = items.into_par_iter().map(|elem| {
                    let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    sub_state.locals = state.locals.clone();
                    sub_state.locals.push((elem.clone(), Env::new()));
                    let sub_env = base_env.extend(&var_name, elem.clone());
                    let (res, _, _) = super::run_vm(sub_state, funcs, &sub_env)?;
                    let is_true = res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).is_truthy()).unwrap_or(false);
                    if is_true {
                        Ok(Some(elem))
                    } else {
                        Ok(None)
                    }
                }).collect();
                
                let filtered: Vec<Atom> = mapped?.into_iter().flatten().collect();
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(filtered))]));
                state.ip += 1;
            }
            Opcode::Once { body_code, free_vars_map } => {
                // Once: single sub-VM, no loop state needed.
                struct OnceResume;
                let (res, exit_status) = match state.resume_data.take().and_then(|r| r.downcast::<OnceResume>().ok()) {
                    Some(_) => {
                        let (r, e) = state.last_sub_result.take().unwrap_or_else(|| (Vec::new(), VmExit::Normal));
                        (r, e)
                    }
                    None => {
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        state.resume_data = Some(Box::new(OnceResume));
                        yield_vm!(state, sub_state, base_env.clone());
                    }
                };
                state.budget = state.budget; // budget already updated by trampoline
                match exit_status {
                    VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                    VmExit::Cut => { state.stack.push(res.into_iter().take(1).collect()); state.cut_executed = true; }
                    VmExit::Normal => { state.stack.push(res.into_iter().take(1).collect()); }
                    VmExit::YieldCall { .. } => unreachable!(),
                }
                state.ip += 1;
            }
            Opcode::Progn { bodies, free_vars_map } => {
                // Progn: run each body sequentially, resuming after each.
                struct PrognResume {
                    bodies: Vec<Arc<[Opcode]>>,
                    next_body_idx: usize,
                    last: ResultSet,
                    free_vars_map: Arc<[String]>,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<PrognResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            match sub_exit {
                                VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                                VmExit::Cut => { r.last = sub_res; state.cut_executed = true; r.next_body_idx = r.bodies.len(); }
                                VmExit::Normal => { r.last = sub_res; }
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        PrognResume { bodies: bodies.clone(), next_body_idx: 0, last: Vec::new(), free_vars_map: free_vars_map.clone() }
                    }
                };
                while resume.next_body_idx < resume.bodies.len() && !state.cut_executed {
                    let body_code = resume.bodies[resume.next_body_idx].clone();
                    resume.next_body_idx += 1;
                    let mut sub_state = VMState::new_with_parent(body_code, resume.free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    sub_state.locals = state.locals.clone();
                    state.resume_data = Some(Box::new(resume));
                    yield_vm!(state, sub_state, base_env.clone());
                }
                state.stack.push(resume.last);
                state.ip += 1;
            }
            Opcode::Prog1 { bodies, free_vars_map } => {
                // Prog1: run each body, return first result.
                struct Prog1Resume {
                    bodies: Vec<Arc<[Opcode]>>,
                    next_body_idx: usize,
                    first: ResultSet,
                    free_vars_map: Arc<[String]>,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<Prog1Resume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            match sub_exit {
                                VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                                VmExit::Cut => {
                                    if r.next_body_idx == 1 { r.first = sub_res; }
                                    state.cut_executed = true;
                                    r.next_body_idx = r.bodies.len();
                                }
                                VmExit::Normal => {
                                    if r.next_body_idx == 1 { r.first = sub_res; }
                                }
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        Prog1Resume { bodies: bodies.clone(), next_body_idx: 0, first: Vec::new(), free_vars_map: free_vars_map.clone() }
                    }
                };
                while resume.next_body_idx < resume.bodies.len() && !state.cut_executed {
                    let body_code = resume.bodies[resume.next_body_idx].clone();
                    resume.next_body_idx += 1;
                    let mut sub_state = VMState::new_with_parent(body_code, resume.free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                    sub_state.locals = state.locals.clone();
                    state.resume_data = Some(Box::new(resume));
                    yield_vm!(state, sub_state, base_env.clone());
                }
                state.stack.push(resume.first);
                state.ip += 1;
            }
            Opcode::Chain { steps, final_code, free_vars_map } => {
                // Chain: evaluate each step, bind result, then run final body.
                struct ChainResume {
                    steps: Vec<(Arc<[Opcode]>, String)>,
                    final_code: Arc<[Opcode]>,
                    free_vars_map: Arc<[String]>,
                    next_step_idx: usize,  // 0..steps.len() = steps; steps.len() = final body
                    done: bool,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<ChainResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            let is_final = r.next_step_idx > r.steps.len();
                            let val_opt = match sub_exit {
                                VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                                VmExit::Cut => { state.cut_executed = true; sub_res.into_iter().next().map(|(a,env)| crate::eval::shared::subst::subst_atom(&a,&env)) }
                                VmExit::Normal => sub_res.into_iter().next().map(|(a,env)| crate::eval::shared::subst::subst_atom(&a,&env)),
                                VmExit::YieldCall { .. } => unreachable!(),
                            };
                            if is_final {
                                // Final body just finished — push result and finish.
                                let rs = val_opt.map(|v| plain(vec![v])).unwrap_or_default();
                                state.stack.push(rs);
                                state.ip += 1;
                                continue;
                            } else {
                                // A step finished: bind the var.
                                let step_idx = r.next_step_idx - 1;
                                let var_name = &r.steps[step_idx].1;
                                let val = val_opt.ok_or_else(|| format!("chain: step {} produced no result", var_name))?;
                                if let Some(pos) = state.free_vars_map.iter().position(|x| x == var_name) {
                                    state.free_vars_bindings[pos] = val;
                                } else {
                                    let mut temp = state.free_vars_map.to_vec();
                                    temp.push(var_name.clone());
                                    state.free_vars_map = Arc::from(temp);
                                    state.free_vars_bindings.push(val);
                                }
                            }
                        }
                        r
                    }
                    None => {
                        ChainResume { steps: steps.clone(), final_code: final_code.clone(), free_vars_map: free_vars_map.clone(), next_step_idx: 0, done: false }
                    }
                };
                if !state.cut_executed {
                    if resume.next_step_idx < resume.steps.len() {
                        let (step_code, _) = resume.steps[resume.next_step_idx].clone();
                        resume.next_step_idx += 1;
                        let mut sub_state = VMState::new_with_parent(step_code, resume.free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        state.resume_data = Some(Box::new(resume));
                        yield_vm!(state, sub_state, base_env.clone());
                    } else {
                        // All steps done, run final body.
                        resume.next_step_idx += 1; // mark as final
                        let mut sub_state = VMState::new_with_parent(resume.final_code.clone(), resume.free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        state.resume_data = Some(Box::new(resume));
                        yield_vm!(state, sub_state, base_env.clone());
                    }
                } else {
                    state.stack.push(Vec::new());
                    state.ip += 1;
                }
            }
            Opcode::Within { body_code, free_vars_map } => {
                // Within: single sub-VM.
                struct WithinResume;
                let (res, exit_status) = match state.resume_data.take().and_then(|r| r.downcast::<WithinResume>().ok()) {
                    Some(_) => {
                        let (r, e) = state.last_sub_result.take().unwrap_or_else(|| (Vec::new(), VmExit::Normal));
                        (r, e)
                    }
                    None => {
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        state.resume_data = Some(Box::new(WithinResume));
                        yield_vm!(state, sub_state, base_env.clone());
                    }
                };
                match exit_status {
                    VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                    VmExit::Cut => { state.cut_executed = true; }
                    VmExit::Normal => {}
                    VmExit::YieldCall { .. } => unreachable!(),
                }
                let atoms: Vec<Atom> = res.into_iter().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)).collect();
                if atoms.is_empty() { return Err("within: expression produced no results".into()); }
                let wrapped = Atom::Expr(crate::atom::expr_data(
                    std::iter::once(Atom::sym("within")).chain(atoms).collect::<Vec<_>>()
                ));
                state.stack.push(plain(vec![wrapped]));
                state.ip += 1;
            }
            Opcode::WithMutex { body_code, free_vars_map } => {
                // WithMutex: single sub-VM under a named mutex.
                struct WithMutexResume { mutex_name: String }
                let (res, exit_status) = match state.resume_data.take().and_then(|r| r.downcast::<WithMutexResume>().ok()) {
                    Some(_) => {
                        let (r, e) = state.last_sub_result.take().unwrap_or_else(|| (Vec::new(), VmExit::Normal));
                        (r, e)
                    }
                    None => {
                        let name_rs = state.stack.pop().ok_or("VM stack underflow on WithMutex")?;
                        let mutex_name = name_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).to_sexpr_string()).unwrap_or_default();
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        // WithMutex: the mutex guard spans across the trampoline yield.
                        // We acquire before yield, release after return.
                        // Use a thread-local guard slot to hold it across the yield boundary.
                        // ponytail: mutex held for the duration of the sub-VM via thread-local.
                        let sub_env = base_env.clone();
                        let result = crate::space::mutate::with_named_mutex(&mutex_name, || {
                            // Since we're inside the closure we must run synchronously here.
                            // This is the one site that can't fully trampoline (mutex semantics require
                            // the body to complete before the lock drops). We call run_vm directly.
                            run_vm(sub_state, funcs, &sub_env)
                        })?;
                        state.budget = result.1;
                        state.last_sub_result = Some((result.0, result.2));
                        // Fall through to the resume path below.
                        let (r, e) = state.last_sub_result.take().unwrap_or_else(|| (Vec::new(), VmExit::Normal));
                        (r, e)
                    }
                };
                match exit_status {
                    VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                    VmExit::Cut => { state.cut_executed = true; }
                    VmExit::Normal => {}
                    VmExit::YieldCall { .. } => unreachable!(),
                }
                state.stack.push(res);
                state.ip += 1;
            }
            Opcode::Transaction { body_code, free_vars_map } => {
                // Transaction: snapshot, run body; rollback on empty/error.
                struct TransactionResume { snapshot: crate::space::mutate::TransactionSnapshot }
                let (res, exit_status) = match state.resume_data.take().and_then(|r| r.downcast::<TransactionResume>().ok()) {
                    Some(r) => {
                        let r = *r;
                        let (res, e) = state.last_sub_result.take().unwrap_or_else(|| (Vec::new(), VmExit::Normal));
                        // Handle rollback on the return path.
                        match &e {
                            VmExit::TailCall(_) => {
                                crate::space::mutate::restore_transaction_state(r.snapshot, funcs)
                                    .map_err(|e| format!("transaction: rollback failed: {e}"))?;
                            }
                            _ if res.is_empty() => {
                                crate::space::mutate::restore_transaction_state(r.snapshot, funcs)
                                    .map_err(|e| format!("transaction: rollback failed: {e}"))?;
                            }
                            _ => {}
                        }
                        (res, e)
                    }
                    None => {
                        let snapshot = crate::space::mutate::snapshot_transaction_state(funcs);
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        state.resume_data = Some(Box::new(TransactionResume { snapshot }));
                        yield_vm!(state, sub_state, base_env.clone());
                    }
                };
                match exit_status {
                    VmExit::TailCall(locs) => return Ok((Vec::new(), state.budget, VmExit::TailCall(locs))),
                    VmExit::Cut => { state.cut_executed = true; }
                    VmExit::Normal => {}
                    VmExit::YieldCall { .. } => unreachable!(),
                }
                state.stack.push(res);
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
                    Some(Atom::Sym(s)) => std::sync::Arc::from(s.as_str()),
                    Some(Atom::Str(s)) => s.clone(),
                    Some(Atom::Expr(expr)) if expr.len() == 2 => {
                        if let (Some(Atom::Sym(head)), Some(py_atom)) = (expr.get(0), expr.get(1)) {
                            if head.as_ref() == "library" {
                                match py_atom {
                                    Atom::Sym(py) => std::sync::Arc::from(py.as_str()),
                                    Atom::Str(py) => py.clone(),
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
                // MapAtomPatternLambda: resumable pattern-filtered map.
                struct MapAtomPatternResume {
                    items: Vec<Atom>,
                    next_item_idx: usize,
                    mapped_results: Vec<Atom>,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<MapAtomPatternResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            if let Some((val, env)) = sub_res.into_iter().next() {
                                r.mapped_results.push(crate::eval::shared::subst::subst_atom(&val, &env));
                            }
                            match sub_exit {
                                VmExit::Cut => { state.cut_executed = true; }
                                VmExit::TailCall(locs) => return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(r.mapped_results))]), state.budget, VmExit::TailCall(locs))),
                                VmExit::Normal => {}
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        let list_rs = state.stack.pop().ok_or("VM stack underflow on MapAtomPatternLambda")?;
                        let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                            Some(Atom::Expr(v)) => v.to_vec(),
                            Some(other) => vec![other],
                            None => return Err("map-atom: list arg produced no result".to_string()),
                        };
                        let cap = items.len();
                        MapAtomPatternResume { items, next_item_idx: 0, mapped_results: Vec::with_capacity(cap) }
                    }
                };
                while resume.next_item_idx < resume.items.len() && !state.cut_executed {
                    let elem = resume.items[resume.next_item_idx].clone();
                    resume.next_item_idx += 1;
                    let matched = crate::eval::shared::pattern::try_match_one(pattern, &elem, &base_env, funcs)?;
                    if let Some(matched_env) = matched {
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        for var in pattern_vars {
                            let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                            sub_state.locals.push((bound, Env::new()));
                        }
                        state.resume_data = Some(Box::new(resume));
                        yield_vm!(state, sub_state, matched_env);
                    }
                    // no match: skip element, continue loop without yielding
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(resume.mapped_results))]));
                state.ip += 1;
            }
            Opcode::FilterAtomPatternLambda {
                pattern,
                body_code,
                pattern_vars,
                free_vars_map,
            } => {
                // FilterAtomPatternLambda: resumable pattern-filtered filter.
                struct FilterAtomPatternResume {
                    items: Vec<Atom>,
                    next_item_idx: usize,
                    filtered_results: Vec<Atom>,
                }
                let mut resume = match state.resume_data.take().and_then(|r| r.downcast::<FilterAtomPatternResume>().ok()) {
                    Some(r) => {
                        let mut r = *r;
                        if let Some((sub_res, sub_exit)) = state.last_sub_result.take() {
                            let is_true = sub_res.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env).is_truthy()).unwrap_or(false);
                            if is_true {
                                r.filtered_results.push(r.items[r.next_item_idx - 1].clone());
                            }
                            match sub_exit {
                                VmExit::Cut => { state.cut_executed = true; }
                                VmExit::TailCall(locs) => return Ok((plain(vec![Atom::Expr(crate::atom::expr_data(r.filtered_results))]), state.budget, VmExit::TailCall(locs))),
                                VmExit::Normal => {}
                                VmExit::YieldCall { .. } => unreachable!(),
                            }
                        }
                        r
                    }
                    None => {
                        let list_rs = state.stack.pop().ok_or("VM stack underflow on FilterAtomPatternLambda")?;
                        let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, env)| crate::eval::shared::subst::subst_atom(&a, &env)) {
                            Some(Atom::Expr(v)) => v.to_vec(),
                            Some(other) => vec![other],
                            None => return Err("filter-atom: list arg produced no result".to_string()),
                        };
                        let cap = items.len();
                        FilterAtomPatternResume { items, next_item_idx: 0, filtered_results: Vec::with_capacity(cap) }
                    }
                };
                while resume.next_item_idx < resume.items.len() && !state.cut_executed {
                    let elem = resume.items[resume.next_item_idx].clone();
                    resume.next_item_idx += 1;
                    let matched = crate::eval::shared::pattern::try_match_one(pattern, &elem, &base_env, funcs)?;
                    if let Some(matched_env) = matched {
                        let mut sub_state = VMState::new_with_parent(body_code.clone(), free_vars_map.clone(), state.budget, &state.free_vars_map, &state.free_vars_bindings);
                        sub_state.locals = state.locals.clone();
                        for var in pattern_vars {
                            let bound = matched_env.get(var).unwrap_or(Atom::sym("()"));
                            sub_state.locals.push((bound, Env::new()));
                        }
                        state.resume_data = Some(Box::new(resume));
                        yield_vm!(state, sub_state, matched_env);
                    }
                    // no match: skip, continue
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(resume.filtered_results))]));
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
                                        pure: !body_has_side_effect(&clause.body_code),
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
                                    pure: !body_has_side_effect(&clause.body_code),
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

            // Memoize pure functions (native AND user-defined).
            // is_pure_fn returns false for unknown symbols — safe for all callers.
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
                                    pure: !body_has_side_effect(&clause.body_code),
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
                    let code_arc: std::sync::Arc<[Opcode]> = std::sync::Arc::from(code);

                    let mut locals_to_push = Vec::with_capacity(comp.locals.len());
                    for var in &comp.locals {
                        let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                        locals_to_push.push((val, Env::new()));
                    }

                    pending_calls.push(super::state::PendingCall {
                        body_code: code_arc.clone(),
                        free_vars: Arc::from(comp.free_vars),
                        body_env,
                        locals_to_push,
                        cost: 0,
                        pure: !body_has_side_effect(&code_arc),
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

/// ponytail: scan body code for side-effect opcodes — exits early on first hit.
/// Used to decide whether pending calls can be run in parallel.
fn body_has_side_effect(body_code: &[Opcode]) -> bool {
    body_code.iter().any(|op| matches!(
        op,
        Opcode::AddAtom { .. }
            | Opcode::RemAtom { .. }
            | Opcode::PythonImport { .. }
            | Opcode::ImportDynamic
            | Opcode::Println
            | Opcode::Readln
            | Opcode::PyCall { .. }
            | Opcode::PyEval { .. }
            | Opcode::ImportFile { .. }
            | Opcode::MapAtomLambda { .. }
            | Opcode::FilterAtomLambda { .. }
            | Opcode::MapAtomPatternLambda { .. }
            | Opcode::FilterAtomPatternLambda { .. }
    ))
}

/// ponytail: run a single PendingCall body inside a fresh VMState snapshot.
/// Called by par_iter in the parallel drain path; each invocation is fully independent.
/// Takes free var map and bindings directly so no full VMState needs to be cloned.
/// Budget already validated before parallel dispatch; sub-calls don't track it recursively.
fn run_call_body(
    pending: &super::state::PendingCall,
    funcs: &FnTable,
    fv_map: &Arc<[String]>,
    fv_bindings: &[Atom],
) -> Result<Vec<(Atom, Env)>, String> {
    let free_vars_bindings: Vec<Atom> = pending.free_vars
        .iter()
        .map(|name| {
            if let Some(pos) = fv_map.iter().position(|x| x == name) {
                fv_bindings[pos].clone()
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

    let call_state = VMState {
        code: pending.body_code.clone(),
        ip: 0,
        locals: pending.locals_to_push.clone(),
        stack: Vec::new(),
        free_vars_map: pending.free_vars.clone(),
        free_vars_bindings,
        frames: Vec::new(),
        budget: None, // ponytail: budget already validated at parallel drain entry
        cut_executed: false,
        resume_data: None,
        last_sub_result: None,
    };

    let (results, _, _) = super::run_vm(call_state, funcs, &pending.body_env)?;
    Ok(results)
}

/// Run the next iteration of the Call opcode in flat frame-based control flow.
fn run_next_call_iteration(state: &mut VMState, funcs: &FnTable) -> Result<Option<Env>, String> {
    // ponytail: peek at the full pending queue.
    // When all calls are pure and there's enough work to amortize thread overhead,
    // drain the ENTIRE queue in one parallel pass instead of one call per invocation.
    let (all_pure, pending_len) = {
        let frame = match state.frames.last_mut() {
            Some(f) => f,
            None => return Ok(None),
        };
        let kind = &frame.kind;
        if let CallFrameKind::Call { pending_calls, next_idx, .. } = kind {
            let remaining = pending_calls.len().saturating_sub(*next_idx);
            (remaining > 0 && pending_calls[*next_idx..].iter().all(|p| p.pure), remaining)
        } else {
            return Ok(None);
        }
    };

    let should_parallel = all_pure && pending_len > 1;

    if should_parallel {
        // --- Parallel drain: run ALL remaining pure calls at once ---
        // Extract pending info BEFORE any borrow conflict; frame is only borrowed here.
        let frame = match state.frames.last_mut() {
            Some(f) => f,
            None => return Ok(None),
        };
        let CallFrameKind::Call { pending_calls, next_idx, .. } = &mut frame.kind else {
            return Ok(None);
        };
        let remaining: Vec<_> = pending_calls[*next_idx..].to_vec();
        let total_cost: i64 = remaining.iter().map(|p| p.cost).sum();
        *next_idx = pending_calls.len(); // consume all

        // Capture only what run_call_body needs from parent state.
        let fv_map = state.free_vars_map.clone();
        let fv_bindings = state.free_vars_bindings.clone();

        // Extract budget value BEFORE taking &mut state.budget in parallel loop.
        // Cannot double-borrow state.budget: once for check, once for &mut Option<i64>.
        let initial_budget = state.budget;
        if let Some(b) = initial_budget {
            if b <= total_cost {
                return Err("Budget exhausted".into());
            }
        }
        let budget_for_calls = initial_budget.map(|b| b - total_cost);

        let mut budget_ref = budget_for_calls;
        let results: Vec<(Atom, Env)> = {
            // Collect parallel results; errors collected but not yet propagated.
            let raw: Vec<Result<Vec<(Atom, Env)>, String>> = remaining
                .into_par_iter()
                .map(|pending| run_call_body(&pending, funcs, &fv_map, &fv_bindings))
                .collect();
            // Propagate first error, or flatten all results on success.
            let mut out = Vec::new();
            for r in raw {
                match r {
                    Ok(rs) => out.extend(rs),
                    Err(e) => return Err(e),
                }
            }
            out
        };
        state.budget = budget_ref;

        // Save parent's locals before popping the frame — mirrors what the serial
        // path does at line 2999 (frame.saved_locals = parent_locals). Without this,
        // frame.saved_locals stays Vec::new() and restoring it wipes the parent locals.
        if let Some(frame) = state.frames.last_mut() {
            let parent_locals = std::mem::take(&mut state.locals);
            frame.saved_locals = parent_locals;
        }

        // Push results and fall through to the normal "frame done" path
        let frame = state.frames.pop().unwrap();
        if let CallFrameKind::Call { memo_key, .. } = frame.kind {
            if let Some(key) = memo_key {
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
    } else {
        // --- Serial path: one call per invocation (original logic) ---
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

                    to_run = Some((
                        pending.body_code.clone(),
                        pending.free_vars.clone(),
                        pending.body_env.clone(),
                        pending.locals_to_push.clone(),
                    ));
                }
            }
        }

        if let Some((body_code, free_vars_map, body_env, locals_to_push)) = to_run {
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
