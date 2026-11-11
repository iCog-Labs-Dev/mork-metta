use std::collections::{BTreeSet, HashMap, HashSet};
use std::ffi::{CStr, CString, c_char, c_int};
use std::ptr;
use std::sync::Arc;
use crate::atom::{Atom, Numeric};
use crate::env::{Env, EnvNode};
use crate::eval::machine::budget::ResultSet;
use crate::eval::prolog::convert::{VarMap, atom_to_term, goal_to_term, term_to_atom};
use crate::eval::prolog::engine::{self, with_engine, EngineManager};
use crate::eval::prolog::error::PrologError;
use crate::eval::shared::env::lookup;
use crate::eval::prolog::ffi::{
    Api, CVT_WRITE, PL_Q_CATCH_EXCEPTION, PL_Q_EXT_STATUS, PL_Q_NODEBUG, PL_Q_NORMAL,
    PL_S_EXCEPTION, PL_S_LAST, PL_S_TRUE, predicate_t, qid_t, term_t,
};

enum StepStatus { True, Last, False, Exception(String) }

fn sys_pred(api: &Api, name: &[u8], arity: c_int) -> predicate_t {
    unsafe { api.predicate(name.as_ptr() as *const _, arity, b"system\0".as_ptr() as *const _) }
}

fn next_solution(api: &Api, qid: qid_t) -> StepStatus {
    match unsafe { api.next_solution(qid) } {
        PL_S_LAST => StepStatus::Last,
        PL_S_TRUE => StepStatus::True,
        PL_S_EXCEPTION => StepStatus::Exception(read_exception(api, qid)),
        _ => StepStatus::False,
    }
}

fn read_exception(api: &Api, qid: qid_t) -> String {
    unsafe {
        let ex = api.exception(qid);
        let mut ptr: *const c_char = ptr::null();
        let msg = if ex != 0 && api.get_chars(ex, &mut ptr, CVT_WRITE) != 0 && !ptr.is_null() {
            CStr::from_ptr(ptr).to_string_lossy().into_owned()
        } else {
            "unknown Prolog exception".to_string()
        };
        api.clear_exception();
        msg
    }
}

fn open_query(api: &Api, pred: predicate_t, args: term_t, flags: c_int) -> Result<qid_t, PrologError> {
    let qid = unsafe { api.open_query(0, flags, pred, args) };
    if qid == 0 { return Err(PrologError::Internal("PL_open_query returned NULL".into())); }
    Ok(qid)
}

fn open_call(api: &Api, goal: term_t) -> Result<qid_t, PrologError> {
    open_query(api, sys_pred(api, b"call\0", 1), goal, PL_Q_CATCH_EXCEPTION | PL_Q_EXT_STATUS | PL_Q_NODEBUG)
}

fn run_once(api: &Api, pred: predicate_t, args: term_t, flags: c_int) -> Result<c_int, PrologError> {
    Ok(unsafe { api.call_predicate(0, flags, pred, args) })
}

fn with_frame<R>(api: &Api, f: impl FnOnce() -> Result<R, PrologError>) -> Result<R, PrologError> {
    let frame = unsafe { api.open_foreign_frame() };
    let result = f();
    unsafe { api.discard_foreign_frame(frame) };
    result
}

fn with_main_frame<R>(f: impl FnOnce(&Api) -> Result<R, PrologError>) -> Result<R, PrologError> {
    engine::manager()?.with_main(|api| with_frame(api, || f(api)))?
}

pub fn init_support(manager: &Arc<EngineManager>) -> Result<(), PrologError> {
    let code = r#"
:- dynamic '&self'/1, '&self'/2, '&self'/3, '&self'/4, '&self'/5, '&self'/6, '&self'/7, '&self'/8.
'+'(X, Y, Z) :- Z is X + Y. '-'(X, Y, Z) :- Z is X - Y.
'*'(X, Y, Z) :- Z is X * Y. '/'(X, Y, Z) :- Z is X / Y.
'mod'(X, Y, Z) :- Z is X mod Y. 'rem'(X, Y, Z) :- Z is X rem Y.
'abs'(X, Y) :- Y is abs(X). '<='(X, Y) :- X =< Y.
'$arity_of'(Name, A) :- current_predicate(user:Name/A).
:- multifile user:file_search_path/2.
:- dynamic user:file_search_path/2.
user:file_search_path(library, './lib').
user:file_search_path(library, 'lib').
"#;
    load_prolog_code(manager, code)
}

pub fn load_prolog_code(manager: &Arc<EngineManager>, code: &str) -> Result<(), PrologError> {
    manager.with_main(|api| with_frame(api, || unsafe {
        let (sargs, c_code) = (api.new_term_refs(2), CString::new(code)?);
        api.put_string_chars(sargs, c_code.as_ptr());
        if api.call_predicate(0, PL_Q_NORMAL, sys_pred(api, b"open_string\0", 2), sargs) == 0 {
            return Err(PrologError::Internal("failed to open_string".into()));
        }
        let lf_args = api.new_term_refs(2);
        api.put_atom_chars(lf_args, b"user\0".as_ptr() as *const _);
        let (opt, opts) = (api.new_term_ref(), api.new_term_ref());
        api.cons_functor_v(opt, api.new_functor(api.new_atom(b"stream\0".as_ptr() as *const _), 1), sargs + 1);
        api.put_nil(opts);
        api.cons_list(opts, opt, opts);
        api.put_term(lf_args + 1, opts);
        api.call_predicate(0, PL_Q_NORMAL, sys_pred(api, b"load_files\0", 2), lf_args);
        Ok(())
    }))?
}

fn run_goal<T>(
    goal: &Atom,
    in_bindings: &[(String, Atom)],
    mut on_solution: impl FnMut(&Api, &VarMap) -> T,
) -> Result<Vec<T>, PrologError> {
    let pooled = engine::manager()?.checkout()?;
    with_engine(pooled.engine(), |api| with_frame(api, || unsafe {
        let mut var_map = VarMap::new();
        for (name, value) in in_bindings {
            let t = atom_to_term(value, api, &mut var_map)?;
            var_map.insert(name.clone(), t);
        }
        let qid = open_call(api, goal_to_term(goal, api, &mut var_map)?)?;
        let mut solutions = Vec::new();
        loop {
            match next_solution(api, qid) {
                StepStatus::True => solutions.push(on_solution(api, &var_map)),
                StepStatus::Last => { solutions.push(on_solution(api, &var_map)); break; }
                StepStatus::False => break,
                StepStatus::Exception(msg) => {
                    api.close_query(qid);
                    return Err(PrologError::Exception(msg));
                }
            }
        }
        api.close_query(qid);
        Ok(solutions)
    }))?
}

pub fn call_predicate_goal(goal: &Atom) -> Result<Vec<Atom>, PrologError> {
    run_goal(goal, &[], |_, _| Atom::sym("true"))
}

pub fn call_function(functor_name: &str, args: &[Atom]) -> Result<Vec<Atom>, PrologError> {
    let pooled = engine::manager()?.checkout()?;
    with_engine(pooled.engine(), |api| with_frame(api, || unsafe {
        let mut var_map = VarMap::new();
        let (c_head, arity) = (CString::new(functor_name)?, args.len() + 1);
        let a0 = api.new_term_refs(arity as c_int);
        for (i, arg) in args.iter().enumerate() {
            api.put_term(a0 + i, atom_to_term(arg, api, &mut var_map)?);
        }
        let result_term = a0 + args.len();
        api.put_variable(result_term);
        let pred = api.predicate(c_head.as_ptr(), arity as c_int, b"user\0".as_ptr() as *const _);
        let qid = open_query(api, pred, a0, PL_Q_CATCH_EXCEPTION | PL_Q_EXT_STATUS | PL_Q_NODEBUG)?;
        let mut reverse_vars = HashMap::new();
        let mut atoms = Vec::new();
        loop {
            let is_last = match next_solution(api, qid) {
                StepStatus::False => break,
                StepStatus::Last => true,
                StepStatus::True => false,
                StepStatus::Exception(msg) => {
                    api.close_query(qid);
                    if atoms.is_empty() { return Err(PrologError::Exception(msg)); }
                    atoms.push(PrologError::Exception(msg).to_error_atom(&Atom::sym("prolog_stream")));
                    return Ok(atoms);
                }
            };
            match term_to_atom(result_term, api, &mut reverse_vars) {
                Ok(atom) => atoms.push(atom),
                Err(e) if atoms.is_empty() => { api.close_query(qid); return Err(e); }
                Err(e) => {
                    if !is_last { atoms.push(e.to_error_atom(&Atom::sym("prolog_stream"))); }
                    break;
                }
            }
            if is_last { break; }
        }
        api.close_query(qid);
        Ok(atoms)
    }))?
}

pub fn assertz_clause(clause: &Atom) -> Result<(), PrologError> {
    with_main_frame(|api| {
        let t = goal_to_term(clause, api, &mut VarMap::new())?;
        run_once(api, sys_pred(api, b"assertz\0", 1), t, PL_Q_NORMAL).map(|_| ())
    })
}

pub fn retract_clause(clause: &Atom) -> Result<bool, PrologError> {
    with_main_frame(|api| {
        let t = goal_to_term(clause, api, &mut VarMap::new())?;
        Ok(run_once(api, sys_pred(api, b"retract\0", 1), t, PL_Q_NORMAL)? != 0)
    })
}

pub fn consult_file(path: &str) -> Result<(), PrologError> {
    with_main_frame(|api| {
        let c_path = CString::new(path)?;
        let path_term = unsafe { api.new_term_ref() };
        unsafe { api.put_atom_chars(path_term, c_path.as_ptr()) };
        let flags = PL_Q_CATCH_EXCEPTION | PL_Q_NORMAL;
        if run_once(api, sys_pred(api, b"consult\0", 1), path_term, flags)? == 0 {
            return Err(PrologError::Internal(format!("consult failed for {path}")));
        }
        Ok(())
    })
}

pub fn current_arities(name: &str) -> Result<Vec<usize>, PrologError> {
    let goal = Atom::expr(vec![Atom::sym("$arity_of"), Atom::sym(name), Atom::sym("$A")]);
    let arities = run_goal(&goal, &[], |api, var_map| {
        var_map.get("$A").and_then(|&term| term_to_atom(term, api, &mut HashMap::new()).ok())
    })?
    .into_iter()
    .filter_map(|sol| match sol {
        Some(Atom::Num(Numeric::Int(i))) => usize::try_from(i).ok(),
        _ => None,
    })
    .collect::<BTreeSet<_>>();
    Ok(arities.into_iter().collect())
}

pub fn translate_goal(
    goal: &Atom,
    in_bindings: &[(String, Atom)],
) -> Result<Vec<Vec<(String, Atom)>>, PrologError> {
    let mut reverse_vars = HashMap::new();
    run_goal(goal, in_bindings, |api, var_map| {
        var_map
            .iter()
            .filter_map(|(name, &term)| term_to_atom(term, api, &mut reverse_vars).ok().map(|atom| (name.clone(), atom)))
            .collect()
    })
}

pub fn eval_translate_predicate_atom(
    goal: &Atom,
    base_env: &Env,
    free_vars_map: &[String],
    free_vars_bindings: &[Atom],
) -> Result<ResultSet, PrologError> {
    let in_bindings = gather_bindings(base_env, free_vars_map, free_vars_bindings);
    let solutions = translate_goal(goal, &in_bindings)?;
    let find_alias = |name: &str| -> Option<&str> {
        free_vars_map.iter().zip(free_vars_bindings).find_map(|(orig, fresh)| {
            let Atom::Sym(f) = fresh else { return None };
            if orig == name { Some(f.as_str()) }
            else if f.as_str() == name { Some(orig.as_str()) }
            else { None }
        })
    };
    let envs = solutions
        .into_iter()
        .map(|solution| {
            let mut env = base_env.clone();
            for (vname, vval) in solution {
                if matches!(&vval, Atom::Sym(s) if s.starts_with("$_V")) { continue; }
                env = env.extend(&vname, vval.clone());
                if let Some(other) = find_alias(&vname) {
                    env = env.extend(other, vval);
                }
            }
            (Atom::sym("true"), env)
        })
        .collect();
    Ok(envs)
}

fn gather_bindings(
    base_env: &Env,
    free_vars_map: &[String],
    free_vars_bindings: &[Atom],
) -> Vec<(String, Atom)> {
    let mut bindings = Vec::new();
    let mut seen = HashSet::new();
    let mut curr = base_env.clone();
    let mut todo = Vec::new();
    loop {
        match curr.inner() {
            EnvNode::Empty => match todo.pop() {
                Some(next) => curr = next,
                None => break,
            },
            EnvNode::Cons { name, value, next } => {
                if seen.insert(name.to_string()) { bindings.push((name.to_string(), (**value).clone())); }
                curr = next.clone();
            }
            EnvNode::Link { prefix, base } => {
                todo.push(base.clone());
                curr = prefix.clone();
            }
        }
    }
    for (idx, name) in free_vars_map.iter().enumerate() {
        let Some(Atom::Sym(fresh_s)) = free_vars_bindings.get(idx) else { continue };
        let Some(bound_val) = lookup(base_env, fresh_s) else { continue };
        if seen.insert(name.clone()) { bindings.push((name.clone(), bound_val.clone())); }
        if seen.insert(fresh_s.to_string()) { bindings.push((fresh_s.to_string(), bound_val)); }
    }
    bindings
}

pub fn sync_space(atoms: &[Atom]) -> Result<(), PrologError> {
    with_main_frame(|api| unsafe {
        let c_code = CString::new(
            "forall(current_predicate('&self'/A), (functor(H, '&self', A), retractall(H))).",
        )
        .unwrap();
        let term = api.new_term_ref();
        api.chars_to_term(c_code.as_ptr(), term);
        api.call(term, api.new_module(api.new_atom(b"user\0".as_ptr() as *const _)));
        let self_atom = api.new_atom(b"&self\0".as_ptr() as *const _);
        let assertz = sys_pred(api, b"assertz\0", 1);
        for atom in atoms {
            let Atom::Expr(items) = atom else { continue };
            if items.is_empty() { continue; }
            let mut var_map = VarMap::new();
            let a0 = api.new_term_refs(items.len() as c_int);
            let ok = items.iter().enumerate().all(|(i, it)| match atom_to_term(it, api, &mut var_map) {
                Ok(t) => { api.put_term(a0 + i, t); true }
                Err(_) => false,
            });
            if !ok { continue; }
            let clause_term = api.new_term_ref();
            let f = api.new_functor_sz(self_atom, items.len());
            if api.cons_functor_v(clause_term, f, a0) != 0 {
                let _ = run_once(api, assertz, clause_term, PL_Q_NORMAL);
            }
        }
        Ok(())
    })
}
