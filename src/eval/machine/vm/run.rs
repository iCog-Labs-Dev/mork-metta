use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use crate::func::{FnTable, FunctionKind};
use crate::eval::machine::budget::{ResultSet, plain};
use super::op::Opcode;
use super::state::VMState;
use std::sync::Arc;

pub fn run_vm(
    mut state: VMState,
    funcs: &FnTable,
    base_env: &Env,
) -> Result<(ResultSet, Option<i64>, bool), String> {
    let debug_vm = std::env::var_os("MORK_DEBUG_VM").is_some();
    if debug_vm {
        eprintln!("--- VM CODE ---");
        for (i, op) in state.code.iter().enumerate() {
            eprintln!("{:03}: {:?}", i, op);
        }
        eprintln!("----------------");
    }

    while state.ip < state.code.len() {
        let op = &state.code[state.ip];
        if debug_vm {
            eprintln!("IP: {:03} | OP: {:?} | STACK: {:?} | LOCALS: {:?}", state.ip, op, state.stack, state.locals);
        }
        match op {
            Opcode::Const(atom) => {
                state.stack.push(plain(vec![atom.clone()]));
                state.ip += 1;
            }
            Opcode::Load(idx) => {
                let (val, env) = state.locals[*idx as usize].clone();
                let resolved = match &val {
                    Atom::Sym(s) if s.starts_with('$') => {
                        crate::eval::shared::env::lookup(&env, s)
                            .or_else(|| crate::eval::shared::env::lookup(base_env, s))
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
                        crate::eval::shared::env::lookup(base_env, s).unwrap_or(fresh)
                    }
                    _ => fresh,
                };
                state.stack.push(plain(vec![resolved]));
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
            Opcode::AddAtom => {
                let atom_rs = state.stack.pop().ok_or("VM stack underflow on AddAtom")?;
                if let Some((atom, _)) = atom_rs.first() {
                    let cost = crate::eval::machine::budget::calculate_cost(atom).unwrap_or(0);
                    if let Some(b) = state.budget {
                        if b <= cost {
                            return Err("Budget exhausted".into());
                        }
                        state.budget = Some(b - cost);
                    }
                    funcs.space.write().unwrap().add_atom(atom)?;
                    state.stack.push(plain(vec![Atom::sym("()")]));
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::RemAtom => {
                let atom_rs = state.stack.pop().ok_or("VM stack underflow on RemAtom")?;
                if let Some((atom, _)) = atom_rs.first() {
                    let cost = crate::eval::machine::budget::calculate_cost(atom).unwrap_or(0);
                    if let Some(b) = state.budget {
                        if b <= cost {
                            return Err("Budget exhausted".into());
                        }
                        state.budget = Some(b - cost);
                    }
                    funcs.space.write().unwrap().remove_atom(atom)?;
                    state.stack.push(plain(vec![Atom::sym("()")]));
                } else {
                    state.stack.push(Vec::new());
                }
                state.ip += 1;
            }
            Opcode::Call(arity) => {
                let head_rs = state.stack.pop().ok_or("VM stack underflow on Call head")?;
                let mut arg_sets = Vec::with_capacity(*arity as usize);
                for _ in 0..*arity {
                    arg_sets.push(state.stack.pop().ok_or("VM stack underflow on Call arg")?);
                }
                arg_sets.reverse();
                
                let head = head_rs.first().map(|(a, _)| a.clone()).unwrap_or(Atom::sym("()"));
                match head {
                    Atom::Sym(ref name) => {
                        if let Some(function) = funcs.get(name, *arity) {
                            match &function.kind {
                                FunctionKind::Native { func: native_f } => {
                                    let mut buf = Vec::new();
                                    let mut results = Vec::new();
                                    super::super::apply::cartesian_product_apply::<String>(&arg_sets, &mut buf, &mut |slice: &[Atom]| {
                                        let res = native_f(slice, funcs)?;
                                        results.extend(res.into_iter());
                                        Ok(())
                                    })?;
                                    state.stack.push(plain(results));
                                }
                            }
                        } else {
                            // User function call lookup
                            let combos = super::super::apply::threaded_combinations(&arg_sets);
                            let mut results = Vec::new();
                            if let Some(clauses) = crate::eval::forms::query::lookup_user_clauses(name, *arity, funcs) {
                                'combos_loop: for (combo, combo_env) in combos {
                                    for (patterns, body) in &clauses {
                                        if let Some((body_env, subst_cost)) = crate::eval::forms::query::match_clause(patterns, &combo, &combo_env, funcs) {
                                            let mut comp = super::compiler::VMCompiler::new(patterns, Some(name.to_string()));
                                            let mut code = Vec::new();
                                            if comp.compile(body, &mut code, true).is_ok() {
                                                // Debit structural budget cost prior to body evaluation
                                                let body_cost = crate::eval::machine::budget::calculate_expr_cost(body);
                                                let total_cost = subst_cost + body_cost;
                                                if let Some(b) = state.budget {
                                                    if b <= total_cost {
                                                        return Err("Budget exhausted".into());
                                                    }
                                                    state.budget = Some(b - total_cost);
                                                }
                                                let mut sub_state = VMState::new_with_parent(
                                                    code,
                                                    comp.free_vars,
                                                    state.budget,
                                                    &state.free_vars_map,
                                                    &state.free_vars_bindings,
                                                );
                                                for var in &comp.locals {
                                                    let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                                                    sub_state.locals.push((val, Env::new()));
                                                }
                                                let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &body_env)?;
                                                state.budget = sub_budget;
                                                results.extend(res);
                                                if cut_executed {
                                                    state.cut_executed = true;
                                                    break 'combos_loop;
                                                }
                                            } else {
                                                // Fallback to CEK machine for this clause body
                                                let body_cost = crate::eval::machine::budget::calculate_expr_cost(body);
                                                let total_cost = subst_cost + body_cost;
                                                if let Some(b) = state.budget {
                                                    if b <= total_cost {
                                                        return Err("Budget exhausted".into());
                                                    }
                                                    state.budget = Some(b - total_cost);
                                                }
                                                let body_rs = super::super::step::run_rs(Arc::new(body.clone()), body_env, funcs, &mut state.budget)?;
                                                results.extend(body_rs);
                                            }
                                        }
                                    }
                                }
                            } else if funcs.has_higher_arity(name, *arity as usize) {
                                let partial_args: Vec<Atom> = arg_sets.iter().flatten().map(|(a, _)| a.clone()).collect();
                                results.push((
                                    Atom::Expr(crate::atom::expr_data([
                                        Atom::sym("partial"),
                                        Atom::Sym(name.clone()),
                                        Atom::Expr(crate::atom::expr_data(partial_args)),
                                    ])),
                                    Env::new(),
                                ));
                            } else {
                                // Data constructor fallback
                                for (combo, combo_env) in combos {
                                    let mut items = vec![Atom::sym(name)];
                                    items.extend(combo);
                                    let substituted: Vec<Atom> = items
                                        .iter()
                                        .map(|a| crate::eval::shared::subst::subst_atom(a, &combo_env))
                                        .collect();
                                    results.push((Atom::Expr(crate::atom::expr_data(substituted)), combo_env));
                                }
                            }
                            state.stack.push(results);
                        }
                    }
                    Atom::Closure(ref c) => {
                        // ponytail: apply anonymous closure by matching arguments and running the body in sub-VM
                        let clauses: Vec<(Vec<Expr>, Expr)> = vec![(c.params.clone(), c.body.clone())];
                        let combos_with_envs = super::super::apply::threaded_combinations(&arg_sets);
                        let mut results = Vec::new();
                        for (combo, combo_env) in combos_with_envs {
                            for (patterns, body) in &clauses {
                                if let Some((body_env, _subst_cost)) = crate::eval::forms::query::match_clause(patterns, &combo, &combo_env, funcs) {
                                    let body = crate::eval::shared::fresh::rename_apart_unbound_vars(
                                        body,
                                        patterns,
                                    );
                                    let mut comp = super::compiler::VMCompiler::new(patterns, None);
                                    let mut code = Vec::new();
                                    if comp.compile(&body, &mut code, false).is_ok() {
                                        let mut sub_state = VMState::new_with_parent(
                                            code,
                                            comp.free_vars,
                                            state.budget,
                                            &state.free_vars_map,
                                            &state.free_vars_bindings,
                                        );
                                        for var in &comp.locals {
                                            let val = body_env.get(var).unwrap_or(Atom::sym("()"));
                                            sub_state.locals.push((val, Env::new()));
                                        }
                                        let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &body_env)?;
                                        state.budget = sub_budget;
                                        results.extend(res);
                                        if cut_executed {
                                            state.cut_executed = true;
                                            break;
                                        }
                                    } else {
                                        let body_rs = super::super::step::run_rs(Arc::new(body), body_env, funcs, &mut state.budget)?;
                                        results.extend(body_rs);
                                    }
                                }
                            }
                        }
                        state.stack.push(results);
                    }
                    _ => {
                        let mut sets = vec![head_rs];
                        sets.extend(arg_sets);
                        let combos = super::super::apply::threaded_combinations(&sets);
                        let mut lists = Vec::new();
                        for (combo, combo_env) in combos {
                            let substituted: Vec<Atom> = combo
                                .iter()
                                .map(|a| crate::eval::shared::subst::subst_atom(a, &combo_env))
                                .collect();
                            lists.push((Atom::Expr(crate::atom::expr_data(substituted)), combo_env));
                        }
                        state.stack.push(lists);
                    }
                }
                state.ip += 1;
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
                let val_rs = state.stack.pop().ok_or("VM stack underflow on Collapse")?;
                let atoms: Vec<Atom> = val_rs.into_iter().map(|(a, _)| a).collect();
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(atoms))]));
                state.ip += 1;
            }
            Opcode::Superpose(count) => {
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
            Opcode::EvalCEK(expr, local_names) => {
                // Reconstruct env from active local bindings
                let mut current_env = base_env.clone();
                for (i, name) in local_names.iter().enumerate() {
                    if let Some((val, _val_env)) = state.locals.get(i) {
                        current_env = crate::eval::shared::env::prepend_chain(
                            crate::eval::shared::env::bind(&Env::new(), name, val.clone()),
                            &current_env,
                        );
                    }
                }
                let body_cost = crate::eval::machine::budget::calculate_expr_cost(expr);
                if let Some(b) = state.budget {
                    if b <= body_cost {
                        return Err("Budget exhausted".into());
                    }
                    state.budget = Some(b - body_cost);
                }
                let res = super::super::step::run_rs_cek(Arc::new(expr.clone()), current_env, funcs, &mut state.budget)?;
                state.stack.push(res);
                state.ip += 1;
            }
            Opcode::ConstEmpty => {
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
                let nd = crate::eval::io::eval_readln(&[], base_env, funcs)?;
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
                        for matched in matches {
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
                                let bound = matched.bindings.iter()
                                    .find(|(k, _)| k == var)
                                    .map(|(_, v)| v.clone())
                                    .unwrap_or_else(|| {
                                        if let Some(idx) = local_names.iter().position(|x| x == var) {
                                            state.locals[idx].0.clone()
                                        } else {
                                            Atom::sym("()")
                                        }
                                    });
                                sub_state.locals.push((bound, Env::new()));
                            }
                            
                            let sub_env = crate::eval::shared::env::bind_all(&match_env, &matched.bindings);
                            let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &sub_env)?;
                            state.budget = sub_budget;
                            results.extend(res);
                            if cut_executed {
                                state.cut_executed = true;
                                break;
                            }
                        }
                    }
                }
                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::Eval => {
                let val_rs = state.stack.pop().ok_or("VM stack underflow on Eval")?;
                let mut results = Vec::new();
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
                    let mut comp = super::compiler::VMCompiler::new(&[], None);
                    let mut code = Vec::new();
                    if comp.compile(&target_expr, &mut code, false).is_ok() {
                        let sub_state = VMState::new_with_parent(
                            code,
                            comp.free_vars,
                            state.budget,
                            &state.free_vars_map,
                            &state.free_vars_bindings,
                        );
                        let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &target_env)?;
                        state.budget = sub_budget;
                        results.extend(res);
                        if cut_executed {
                            state.cut_executed = true;
                            break;
                        }
                    } else {
                        let res = super::super::step::run_rs(Arc::new(target_expr), target_env, funcs, &mut state.budget)?;
                        results.extend(res);
                    }
                }
                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::If { then_code, else_code, free_vars_map } => {
                let condition_rs = state.stack.pop().ok_or("VM stack underflow on If")?;
                let had_bindings = condition_rs.iter().any(|(_, cond_env)| !cond_env.is_empty_env());
                let mut results = Vec::new();
                for (cond, cond_env) in condition_rs {
                    let is_true = cond.is_truthy();
                    let code_to_run = if is_true { then_code } else { else_code };
                    
                    let mut sub_state = VMState::new_with_parent(
                        code_to_run.clone(),
                        free_vars_map.clone(),
                        state.budget,
                        &state.free_vars_map,
                        &state.free_vars_bindings,
                    );
                    for val in &state.locals {
                        sub_state.locals.push(val.clone());
                    }
                    
                    let branch_env = if is_true {
                        crate::eval::shared::pattern::prepend_env(cond_env, base_env)
                    } else {
                        base_env.clone()
                    };
                    
                    let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &branch_env)?;
                    state.budget = sub_budget;
                    results.extend(res);
                    if cut_executed {
                        state.cut_executed = true;
                        break;
                    }
                }
                let final_results = if had_bindings && results.len() > 1 {
                    let atoms: Vec<Atom> = results
                        .iter()
                        .map(|(atom, env)| crate::eval::shared::subst::subst_atom(atom, env))
                        .collect();
                    plain(vec![Atom::Expr(crate::atom::expr_data(atoms))])
                } else {
                    results
                };
                state.stack.push(final_results);
                state.ip += 1;
            }
            Opcode::Let {
                pattern,
                body_code,
                pattern_vars,
                free_vars_map,
            } => {
                // ponytail: Let match pops value, binds matching pattern variables to locals, and executes the body
                let value_rs = state.stack.pop().ok_or("VM stack underflow on Let")?;
                let mut results = Vec::new();
                for (value, value_env) in &value_rs {
                    if let Some(match_env) = crate::eval::shared::pattern::try_match_one(
                        pattern,
                        value,
                        &Env::new(),
                        funcs,
                    )? {
                        let body_env = crate::eval::shared::env::prepend_chain(match_env, value_env);
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
                            let bound = body_env.get(var).unwrap_or(Atom::sym("()"));
                            sub_state.locals.push((bound, Env::new()));
                        }
                        let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &body_env)?;
                        state.budget = sub_budget;
                        results.extend(res);
                        if cut_executed {
                            state.cut_executed = true;
                            break;
                        }
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
                state.stack.push(results);
                state.ip += 1;
            }
            Opcode::Case { branches, local_names } => {
                let scrutinee_rs = state.stack.pop().ok_or("VM stack underflow on Case")?;
                if scrutinee_rs.is_empty() {
                    let mut evaluated = false;
                    for branch in branches {
                        if matches!(&branch.pattern, Expr::Symbol(s) if s == "Empty") {
                            let sub_state = VMState::new_with_parent(
                                branch.body_code.clone(),
                                branch.free_vars_map.clone(),
                                state.budget,
                                &state.free_vars_map,
                                &state.free_vars_bindings,
                            );
                            let mut sub_locals = Vec::new();
                            for val in &state.locals {
                                sub_locals.push(val.clone());
                            }
                            let mut run_state = sub_state;
                            run_state.locals = sub_locals;
                            let (res, sub_budget, cut_executed) = run_vm(run_state, funcs, base_env)?;
                            state.budget = sub_budget;
                            state.stack.push(res);
                            evaluated = true;
                            if cut_executed {
                                state.cut_executed = true;
                            }
                            break;
                        }
                    }
                    if !evaluated {
                        state.stack.push(Vec::new());
                    }
                } else {
                    let mut results = Vec::new();
                    for (value, value_env) in &scrutinee_rs {
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
                            let mut sub_state = VMState::new_with_parent(
                                branch.body_code.clone(),
                                branch.free_vars_map.clone(),
                                state.budget,
                                &state.free_vars_map,
                                &state.free_vars_bindings,
                            );
                            for val in &state.locals {
                                sub_state.locals.push(val.clone());
                            }
                            for var in &branch.pattern_vars {
                                let bound = body_env.get(var).unwrap_or(Atom::sym("()"));
                                sub_state.locals.push((bound, Env::new()));
                            }
                            let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &body_env)?;
                            state.budget = sub_budget;
                            results.extend(res);
                            if cut_executed {
                                state.cut_executed = true;
                                break;
                            }
                        } else {
                            return Err(format!(
                                "case: no clause matched value {}",
                                value.to_sexpr_string()
                            ));
                        }
                    }
                    state.stack.push(results);
                }
                state.ip += 1;
            }
            Opcode::Foldall => {
                // ponytail: Foldall pops agg-func, init, and generator, then loops using eval_call_vm
                let agg_rs = state.stack.pop().ok_or("VM stack underflow on Foldall agg-func")?;
                let init_rs = state.stack.pop().ok_or("VM stack underflow on Foldall init")?;
                let gen_rs = state.stack.pop().ok_or("VM stack underflow on Foldall generator")?;

                let agg_atom = agg_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "foldall: agg-func produced no value".to_string())?;
                let init_atom = init_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "foldall: init produced no result".to_string())?;
                let gen_values: Vec<Atom> = gen_rs.into_iter().map(|(a, _)| a).collect();

                let (agg_head, agg_env) = match &agg_atom {
                    Atom::Sym(name) => {
                        (Expr::Symbol(name.to_string()), base_env.clone())
                    }
                    Atom::Closure(_) => {
                        (Expr::Symbol("$__foldall_fn".to_string()),
                         crate::eval::shared::env::bind(base_env, "$__foldall_fn", agg_atom.clone()))
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
                    accum = res.into_iter().next().map(|(a, _)| a)
                        .ok_or_else(|| "foldall: agg-func produced no result".to_string())?;
                }
                state.stack.push(plain(vec![accum]));
                state.ip += 1;
            }
            Opcode::Forall => {
                // ponytail: Forall pops check-expr and generator, then verifies truthiness for all values
                let check_rs = state.stack.pop().ok_or("VM stack underflow on Forall check")?;
                let gen_rs = state.stack.pop().ok_or("VM stack underflow on Forall generator")?;

                let check_atom = check_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "forall: check produced no value".to_string())?;
                let gen_values: Vec<Atom> = gen_rs.into_iter().map(|(a, _)| a).collect();

                let check_head = match &check_atom {
                    Atom::Sym(name) => Expr::Symbol(name.to_string()),
                    Atom::Closure(_) => Expr::Symbol("$__check_fn".to_string()),
                    _ => return Err("forall: check must be a function symbol or closure".to_string()),
                };

                let mut is_forall_true = true;
                for val in gen_values {
                    let mut call_env = crate::eval::shared::env::bind(base_env, "$__fv", val);
                    if let Atom::Closure(_) = &check_atom {
                        let check_env = crate::eval::shared::env::bind(base_env, "$__check_fn", check_atom.clone());
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
                    let results: Vec<Atom> = res.into_iter().map(|(a, _)| a).collect();
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
                // ponytail: Foldl pops func, acc, and list, and folds dynamically
                let func_rs = state.stack.pop().ok_or("VM stack underflow on Foldl func")?;
                let acc_rs = state.stack.pop().ok_or("VM stack underflow on Foldl acc")?;
                let list_rs = state.stack.pop().ok_or("VM stack underflow on Foldl list")?;

                let func = func_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "foldl-atom: func arg produced no result".to_string())?;
                let acc = acc_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, _)| a) {
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
                    current_acc = res.into_iter().next().map(|(a, _)| a).unwrap_or(current_acc);
                }
                state.stack.push(plain(vec![current_acc]));
                state.ip += 1;
            }
            Opcode::FoldlLambda {
                var_names,
                body_code,
                free_vars_map,
            } => {
                // ponytail: FoldlLambda aggregates list elements using a precompiled lambda body code for high performance
                let acc_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda acc")?;
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FoldlLambda list")?;

                let acc = acc_rs.into_iter().next().map(|(a, _)| a)
                    .ok_or_else(|| "foldl-atom: acc arg produced no result".to_string())?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, _)| a) {
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
                    let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &step_env)?;
                    state.budget = sub_budget;
                    current_acc = res.into_iter().next().map(|(a, _)| a).unwrap_or(current_acc);
                    if cut_executed {
                        state.cut_executed = true;
                        break;
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
                // ponytail: MapAtomLambda maps list elements using a precompiled lambda body code for high performance
                let list_rs = state.stack.pop().ok_or("VM stack underflow on MapAtomLambda")?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, _)| a) {
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
                    let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &sub_env)?;
                    state.budget = sub_budget;
                    
                    if let Some((val, _)) = res.into_iter().next() {
                        mapped_results.push(val);
                    }
                    if cut_executed {
                        state.cut_executed = true;
                        break;
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
                // ponytail: FilterAtomLambda filters list elements using a precompiled lambda condition code for high performance
                let list_rs = state.stack.pop().ok_or("VM stack underflow on FilterAtomLambda")?;
                let items: Vec<Atom> = match list_rs.into_iter().next().map(|(a, _)| a) {
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
                    let (res, sub_budget, cut_executed) = run_vm(sub_state, funcs, &sub_env)?;
                    state.budget = sub_budget;
                    
                    let is_true = res.into_iter().next().map(|(a, _)| a.is_truthy()).unwrap_or(false);
                    if is_true {
                        filtered_results.push(elem);
                    }
                    if cut_executed {
                        state.cut_executed = true;
                        break;
                    }
                }
                state.stack.push(plain(vec![Atom::Expr(crate::atom::expr_data(filtered_results))]));
                state.ip += 1;
            }
        }
    }

    let final_rs = state.stack.pop().unwrap_or_else(|| plain(Vec::new()));
    let prepended_rs: Vec<(Atom, Env)> = final_rs
        .into_iter()
        .map(|(atom, env)| {
            let merged = crate::eval::shared::env::prepend_chain(env, base_env);
            (atom, merged)
        })
        .collect();
    // ponytail: cut flag is propagated using the 3rd tuple element of run_vm return value to prune loops recursively.
    Ok((prepended_rs, state.budget, state.cut_executed))
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
            code,
            comp.free_vars.clone(),
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
