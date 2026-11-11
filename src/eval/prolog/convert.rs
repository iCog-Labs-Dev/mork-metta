use std::collections::HashMap;
use std::ffi::{CStr, CString, c_char, c_int, c_uint};
use std::ptr;
use std::slice;
use std::sync::Arc;
use crate::atom::{Atom, Numeric};
use crate::eval::prolog::error::PrologError;
use crate::eval::prolog::ffi::{
    Api, CVT_ATOM, CVT_INTEGER, CVT_STRING, PL_ATOM, PL_FLOAT, PL_INTEGER, PL_LIST_PAIR, PL_NIL,
    PL_STRING, PL_TERM, PL_VARIABLE, atom_t, term_t,
};
use crate::eval::prolog::handle::PrologForeign;

pub type VarMap = HashMap<String, term_t>;

pub fn strip_quote_atom(atom: &Atom) -> &Atom {
    match atom {
        Atom::Expr(e) if e.len() == 2 && is_sym(&e[0], "quote") => &e[1],
        _ => atom,
    }
}

fn is_sym(a: &Atom, name: &str) -> bool {
    matches!(a.as_sym(), Ok(s) if s == name)
}

fn conv<T>(r: Result<T, impl ToString>) -> Result<T, PrologError> {
    r.map_err(|e| PrologError::Conversion(e.to_string()))
}

fn get_str(api: &Api, term: term_t, kind: c_uint) -> Result<String, PrologError> {
    let mut ptr: *const c_char = ptr::null();
    if unsafe { api.get_chars(term, &mut ptr, kind) } == 0 || ptr.is_null() {
        return Err(PrologError::Conversion("failed to read Prolog string".into()));
    }
    conv(unsafe { CStr::from_ptr(ptr) }.to_str()).map(str::to_string)
}

pub fn atom_to_term(atom: &Atom, api: &Api, var_map: &mut VarMap) -> Result<term_t, PrologError> {
    let atom = strip_quote_atom(atom);
    let term = unsafe { api.new_term_ref() };
    match atom {
        Atom::Sym(s) => {
            let name = s.as_str();
            if name.starts_with('$') {
                if let Some(&t) = var_map.get(name) {
                    return Ok(t);
                }
                unsafe { api.put_variable(term) };
                var_map.insert(name.to_string(), term);
                return Ok(term);
            }
            unsafe { api.put_atom(term, api.new_atom(CString::new(name)?.as_ptr())) };
        }
        Atom::Str(s) => {
            unsafe { api.put_string_chars(term, CString::new(s.as_ref())?.as_ptr()) };
        }
        Atom::Num(Numeric::Int(i)) => {
            if let Ok(v) = i64::try_from(i) {
                unsafe { api.put_int64(term, v) };
            } else {
                let c_s = CString::new(i.to_string())?;
                if unsafe { api.chars_to_term(c_s.as_ptr(), term) } == 0 {
                    return Err(PrologError::Conversion("failed to parse big int".into()));
                }
            }
        }
        Atom::Num(Numeric::Dec(d)) => {
            unsafe { api.put_float(term, d.to_f64().value()) };
        }
        Atom::Expr(e) => {
            if let Some((head, args)) = extract_predicate_compound(e) {
                return compound(api, head, args, var_map);
            }
            return match &e[..] {
                [head, arg] if is_sym(head, "library") => {
                    compound(api, "library", slice::from_ref(arg), var_map)
                }
                [Atom::Sym(head), args @ ..] if is_prolog_operator(head.as_str()) => {
                    compound(api, head.as_str(), args, var_map)
                }
                _ => list_to_term(api, e, var_map),
            };
        }
        Atom::Gnd(g) => {
            let Some(pf) = g.as_any().downcast_ref::<PrologForeign>() else {
                return Err(PrologError::Conversion("unsupported grounded type".into()));
            };
            if unsafe { api.recorded(pf.record, term) } == 0 {
                return Err(PrologError::Conversion("failed to replay recorded term".into()));
            }
        }
        _ => return Err(PrologError::Conversion("unsupported atom type".into())),
    }
    Ok(term)
}

pub fn goal_to_term(goal: &Atom, api: &Api, var_map: &mut VarMap) -> Result<term_t, PrologError> {
    let goal = strip_quote_atom(goal);
    if let Atom::Expr(items) = goal {
        match &items[..] {
            [sym, _] if is_sym(sym, "Predicate") => atom_to_term(goal, api, var_map),
            [Atom::Sym(head), args @ ..] if is_control(head.as_str()) => {
                let terms: Result<Vec<term_t>, _> =
                    args.iter().map(|arg| goal_to_term(arg, api, var_map)).collect();
                build_compound(api, head.as_str(), &terms?)
            }
            [Atom::Sym(head), args @ ..] => compound(api, head.as_str(), args, var_map),
            _ => atom_to_term(goal, api, var_map),
        }
    } else {
        atom_to_term(goal, api, var_map)
    }
}

fn is_control(s: &str) -> bool {
    matches!(s, ":-" | "?-" | "," | ";" | "->" | "*->" | "\\+" | "not")
}

pub fn is_prolog_operator(s: &str) -> bool {
    is_control(s)
        || matches!(
            s,
            "+" | "-" | "*" | "/" | "mod" | "rem" | "abs" | "min" | "max" | "sqrt" | "**" | "^"
                | "div" | "rdiv" | "=" | "\\=" | "<" | ">" | "=<" | ">=" | "=:=" | "=\\="
        )
}

fn extract_predicate_compound(items: &[Atom]) -> Option<(&str, &[Atom])> {
    match items {
        [head, Atom::Expr(inner)] if is_sym(head, "Predicate") => {
            let (Atom::Sym(pred), args) = inner.split_first()? else { return None };
            Some((pred.as_str(), args))
        }
        [head, Atom::Sym(pred)] if is_sym(head, "Predicate") => Some((pred.as_str(), &[])),
        _ => None,
    }
}

fn build_compound(api: &Api, head: &str, arg_terms: &[term_t]) -> Result<term_t, PrologError> {
    let (head_atom, term) = unsafe { (api.new_atom(CString::new(head)?.as_ptr()), api.new_term_ref()) };
    if arg_terms.is_empty() {
        unsafe { api.put_atom(term, head_atom) };
        return Ok(term);
    }
    let a0 = unsafe { api.new_term_refs(arg_terms.len() as c_int) };
    for (i, &t) in arg_terms.iter().enumerate() {
        unsafe { api.put_term(a0 + i, t) };
    }
    if unsafe { api.cons_functor_v(term, api.new_functor_sz(head_atom, arg_terms.len()), a0) } == 0 {
        return Err(PrologError::Conversion("failed to build compound term".into()));
    }
    Ok(term)
}

fn compound(api: &Api, head: &str, args: &[Atom], var_map: &mut VarMap) -> Result<term_t, PrologError> {
    let terms: Result<Vec<term_t>, PrologError> =
        args.iter().map(|a| atom_to_term(a, api, var_map)).collect();
    build_compound(api, head, &terms?)
}

fn list_to_term(api: &Api, items: &[Atom], var_map: &mut VarMap) -> Result<term_t, PrologError> {
    let list_term = unsafe { api.new_term_ref() };
    unsafe { api.put_nil(list_term) };
    let mut current = list_term;
    for item in items.iter().rev() {
        let head_term = atom_to_term(item, api, var_map)?;
        let new_cell = unsafe { api.new_term_ref() };
        if unsafe { api.cons_list(new_cell, head_term, current) } == 0 {
            return Err(PrologError::Conversion("failed to build list".into()));
        }
        current = new_cell;
    }
    Ok(current)
}

pub fn term_to_atom(
    term: term_t,
    api: &Api,
    reverse_vars: &mut HashMap<usize, String>,
) -> Result<Atom, PrologError> {
    match unsafe { api.term_type(term) } {
        PL_VARIABLE => {
            let name = reverse_vars.entry(term).or_insert_with(|| format!("$_V{term}"));
            Ok(Atom::sym(name))
        }
        PL_ATOM => {
            let s = get_str(api, term, CVT_ATOM)?;
            Ok(if s == "[]" { Atom::expr(vec![]) } else { Atom::sym(&s) })
        }
        PL_STRING => Ok(Atom::str_val(&get_str(api, term, CVT_STRING)?)),
        PL_INTEGER => {
            let mut val: i64 = 0;
            if unsafe { api.get_int64(term, &mut val) } != 0 { return Ok(Atom::num(val as i128)); }
            if let Ok(ibig) = get_str(api, term, CVT_INTEGER).and_then(|s| conv(dashu::integer::IBig::from_str_radix(&s, 10))) {
                return Ok(Atom::Num(Numeric::Int(ibig)));
            }
            Err(PrologError::Conversion("failed to read Prolog integer".into()))
        }
        PL_FLOAT => {
            let mut val: f64 = 0.0;
            if unsafe { api.get_float(term, &mut val) } == 0 {
                return Err(PrologError::Conversion("failed to get float".into()));
            }
            Atom::decimal(&format!("{val}")).map_err(PrologError::Conversion)
        }
        PL_NIL => Ok(Atom::expr(vec![])),
        PL_LIST_PAIR => {
            let mut elements = Vec::new();
            let (head, tail) = unsafe { (api.new_term_ref(), api.new_term_ref()) };
            let mut current = term;
            while unsafe { api.term_type(current) == PL_LIST_PAIR && api.get_list(current, head, tail) != 0 } {
                elements.push(term_to_atom(head, api, reverse_vars)?);
                current = tail;
            }
            if unsafe { api.term_type(current) != PL_NIL } {
                elements.push(term_to_atom(current, api, reverse_vars)?);
            }
            Ok(Atom::expr(elements))
        }
        PL_TERM => {
            let (mut name_atom, mut arity): (atom_t, c_int) = (0, 0);
            if unsafe { api.get_name_arity(term, &mut name_atom, &mut arity) } == 0 {
                return Err(PrologError::Conversion("failed to get functor name and arity".into()));
            }
            let name_ptr = unsafe { api.atom_chars(name_atom) };
            if name_ptr.is_null() {
                return Err(PrologError::Conversion("failed to get functor name chars".into()));
            }
            let mut args = vec![Atom::sym(conv(unsafe { CStr::from_ptr(name_ptr) }.to_str())?)];
            for i in 1..=arity {
                let arg = unsafe { api.new_term_ref() };
                if unsafe { api.get_arg(i, term, arg) } == 0 {
                    return Err(PrologError::Conversion(format!("failed to get arg {i}")));
                }
                args.push(term_to_atom(arg, api, reverse_vars)?);
            }
            Ok(Atom::expr(vec![Atom::sym("Predicate"), Atom::expr(args)]))
        }
        _ => {
            let record = unsafe { api.record(term) };
            if record == 0 {
                return Err(PrologError::Conversion("failed to record foreign term".into()));
            }
            Ok(Atom::Gnd(Arc::new(PrologForeign::new(record))))
        }
    }
}
