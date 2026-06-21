//! Execution of explicit machine transitions.

use super::budget::{calculate_cost, plain, ResultSet};
use super::state::Transition;
use crate::atom::Atom;
use crate::func::FnTable;
// Deduct structural cost of `atom` from `budget` per spec Section 6.
// Returns Err("Budget exhausted for <op>") when insufficient.
fn debit_budget(atom: &Atom, budget: &mut Option<i64>, op: &str) -> Result<(), String> {
    if budget.is_none() { return Ok(()); }
    if let Some(c) = calculate_cost(atom) {
        if let Some(b) = budget {
            if *b <= c {
                return Err(format!("Budget exhausted for {}", op));
            }
            *b -= c;
        }
    }
    Ok(())
}



/// Execute one machine transition and return its produced result set, if any.
pub(crate) fn apply_transition(
    transition: Transition,
    funcs: &FnTable,
    budget: &mut Option<i64>,
) -> Result<Option<ResultSet>, String> {
    match transition {
        Transition::Query { cost } | Transition::Chain { cost } => {
            // debit cost of query / chain transition
            if let Some(b) = budget {
                if *b <= cost {
                    return Err("Budget exhausted".to_string());
                }
                *b -= cost;
            }
            Ok(None)
        }
        Transition::Output => Ok(None),
        Transition::Transform {
            pattern,
            replacement,
        } => {
            let out = crate::space::query::transform_matches(funcs, &pattern, &replacement)?;
            Ok(Some(plain(out)))
        }
        Transition::AddAtom { space_ref, atom } => {
            debit_budget(&atom, budget, "addAtom")?;
            crate::space::mutate::add_atom(funcs, &space_ref, &atom)?;
            Ok(Some(plain(vec![Atom::sym("true")])))
        }
        Transition::RemAtom { space_ref, atom } => {
            debit_budget(&atom, budget, "remAtom")?;
            let removed = crate::space::mutate::remove_atom(funcs, &space_ref, &atom)?;
            Ok(Some(plain(vec![if removed {
                Atom::sym("true")
            } else {
                Atom::sym("")
            }])))
        }
        Transition::WithMutex {
            mutex_name,
            body,
            env,
        } => {
            let res = crate::space::mutate::with_named_mutex(&mutex_name, || {
                super::step::run_rs(body, env, funcs, budget)
            })?;
            Ok(Some(res))
        }
        Transition::Transaction { body, env } => {
            let snapshot = crate::space::mutate::snapshot_transaction_state(funcs);
            match super::step::run_rs(body, env, funcs, budget) {
                Ok(out) => {
                    if out.is_empty() {
                        crate::space::mutate::restore_transaction_state(snapshot, funcs)
                            .map_err(|err| format!("transaction: rollback failed: {err}"))?;
                    }
                    Ok(Some(out))
                }
                Err(err) => {
                    crate::space::mutate::restore_transaction_state(snapshot, funcs).map_err(
                        |restore_err| format!("transaction: rollback failed: {restore_err}"),
                    )?;
                    Err(format!("transaction: {err}"))
                }
            }
        }
    }
}
