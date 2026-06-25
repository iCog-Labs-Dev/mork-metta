//! Runtime state for machine execution.
//!
//! This module defines the data carried while evaluating expressions,
//! including control state, continuation-related state, intermediate results,
//! output, and budget bookkeeping.

use crate::atom::Atom;
use std::collections::HashMap;


/// Return `true` when binding `var` to `atom` would introduce a cycle.
fn occurs_check(var: &str, atom: &Atom, subst: &HashMap<String, Atom>) -> bool {
    match deref(atom, subst) {
        Atom::Sym(symbol) if symbol.starts_with('$') => symbol.as_ref() == var,
        Atom::Expr(items) => items.iter().any(|item| occurs_check(var, item, subst)),
        _ => false,
    }
}

/// Follow variable bindings until a non-variable target is reached.
fn deref(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
    match atom {
        Atom::Sym(symbol) if symbol.starts_with('$') => {
            let mut current = symbol.clone();
            let mut seen = vec![current.clone()];
            loop {
                match subst.get(current.as_ref()) {
                    Some(Atom::Sym(next)) if next.starts_with('$') => {
                        if seen.contains(next) {
                            return Atom::Sym(current.clone());
                        }
                        seen.push(next.clone());
                        current = next.clone();
                    }
                    Some(target) => return target.clone(),
                    None => return Atom::Sym(current.clone()),
                }
            }
        }
        _ => atom.clone(),
    }
}

/// Unify two atoms using an existing substitution map.
fn unify_with_subst(term: &Atom, pattern: &Atom, subst: &mut HashMap<String, Atom>) -> bool {
    let term_deref = deref(term, subst);
    let pattern_deref = deref(pattern, subst);

    match (&term_deref, &pattern_deref) {
        (Atom::Sym(left), Atom::Sym(right))
            if left.starts_with('$') && right.starts_with('$') && left == right =>
        {
            true
        }
        (Atom::Sym(var), other) if var.starts_with('$') => {
            if occurs_check(var, other, subst) {
                false
            } else {
                subst.insert(var.to_string(), other.clone());
                true
            }
        }
        (other, Atom::Sym(var)) if var.starts_with('$') => {
            if occurs_check(var, other, subst) {
                false
            } else {
                subst.insert(var.to_string(), other.clone());
                true
            }
        }
        (Atom::Sym(left), Atom::Sym(right)) => left == right,
        (Atom::Num(left), Atom::Num(right)) => left == right,
        (Atom::Expr(left_items), Atom::Expr(right_items)) => {
            if right_items.len() == 3 && right_items[0] == Atom::sym("=") {
                return unify_with_subst(&term_deref, &right_items[1], subst);
            }
            if left_items.len() != right_items.len() {
                return false;
            }
            left_items
                .iter()
                .zip(right_items.iter())
                .all(|(left, right)| unify_with_subst(left, right, subst))
        }
        _ => false,
    }
}

/// Unify two atoms and return the produced substitution on success.
pub fn unify(term: &Atom, pattern: &Atom) -> Option<HashMap<String, Atom>> {
    let mut subst = HashMap::new();
    if unify_with_subst(term, pattern, &mut subst) {
        Some(subst)
    } else {
        None
    }
}
