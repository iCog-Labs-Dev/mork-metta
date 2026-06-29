//! Builtins for mutable evaluator state and space enumeration.

use crate::atom::Atom;
use crate::builtins::arithmetic::expect_n_args;
use crate::func::{FnTable, NDet};

/// Register state and space builtins.
pub fn register_state_builtins(funcs: &FnTable) {
    funcs.insert_native("get-atoms", 1, |args, table| {
        expect_n_args(args, 1, "get-atoms")?;
        let atoms = table.with_resolved_space(&args[0], |space| Ok(space.get_atoms()))?;
        Ok(NDet::stream(atoms.into_iter()))
    });

    funcs.insert_native("change-state!", 2, |args, table| {
        expect_n_args(args, 2, "change-state!")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.to_string(),
            other => {
                return Err(format!(
                    "change-state!: key must be a symbol, got {}",
                    other.to_sexpr_string()
                ));
            }
        };
        table.state.lock().unwrap().insert(key, args[1].clone());
        Ok(NDet::single(Atom::sym("true")))
    });

    funcs.insert_native("get-state", 1, |args, table| {
        expect_n_args(args, 1, "get-state")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.to_string(),
            other => {
                return Err(format!(
                    "get-state: key must be a symbol, got {}",
                    other.to_sexpr_string()
                ));
            }
        };
        match table.state.lock().unwrap().get(&key) {
            Some(val) => Ok(NDet::single(val.clone())),
            None => Err(format!("get-state: no value for key '{}'", key)),
        }
    });

    funcs.insert_native("bind!", 2, |args, table| {
        expect_n_args(args, 2, "bind!")?;
        let key = match &args[0] {
            Atom::Sym(s) => s.to_string(),
            other => {
                return Err(format!(
                    "bind!: key must be a symbol, got {}",
                    other.to_sexpr_string()
                ));
            }
        };
        let value = match &args[1] {
            Atom::Expr(items) if items.len() == 2 && items[0] == Atom::sym("new-state") => {
                items[1].clone()
            }
            other => other.clone(),
        };
        table.state.lock().unwrap().insert(key, value);
        Ok(NDet::single(Atom::sym("true")))
    });
}
