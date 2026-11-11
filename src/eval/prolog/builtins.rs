use crate::atom::Atom;
use crate::builtins::arithmetic::expect_n_args;
use crate::eval::prolog::error::PrologError;
use crate::eval::prolog::ops;
use crate::func::{FnTable, NDet};
pub fn register_prolog_builtins(funcs: &FnTable) {
    macro_rules! native {
        ($name:literal, |$args:ident, $funcs:tt| $body:expr) => {
            funcs.insert_native($name, 1, |$args, $funcs| {
                expect_n_args($args, 1, $name)?;
                $body
            });
        };
    }
    native!("Predicate", |args, _| Ok(NDet::single(Atom::expr(vec![Atom::sym("Predicate"), args[0].clone()]))));
    native!("callPredicate", |args, _| {
        Ok(match ops::call_predicate_goal(&args[0]).map_err(|e| e.to_string())?.len() {
            0 => NDet::empty(),
            1 => NDet::single(Atom::sym("True")),
            n => NDet::stream((0..n).map(|_| Atom::sym("True"))),
        })
    });
    native!("succeedsPredicate", |args, _| {
        let solutions = ops::call_predicate_goal(&args[0]).map_err(|e| e.to_string())?;
        Ok(NDet::single(Atom::sym(if solutions.is_empty() { "False" } else { "True" })))
    });
    native!("assertzPredicate", |args, _| {
        ops::assertz_clause(&args[0]).map_err(|e| e.to_string())?;
        Ok(NDet::single(Atom::sym("True")))
    });
    native!("retractPredicate", |args, _| {
        let removed = ops::retract_clause(&args[0]).map_err(|e| e.to_string())?;
        Ok(NDet::single(Atom::sym(if removed { "True" } else { "False" })))
    });
    native!("import_prolog_function", |args, funcs_ref| {
        let name_str = name_arg(&args[0], "import_prolog_function")?;
        funcs_ref.imported_prolog_funcs.write().unwrap().insert(name_str.clone());
        if let Ok(arities) = ops::current_arities(&name_str) {
            for arity in arities.into_iter().filter(|&a| a >= 1) {
                register_imported_prolog_function(funcs_ref, &name_str, (arity - 1) as u8);
            }
        }
        Ok(NDet::single(Atom::sym("True")))
    });
    native!("add-translator-rule!", |args, funcs_ref| {
        funcs_ref.translator_rules.write().unwrap().insert(name_arg(&args[0], "add-translator-rule!")?);
        funcs_ref.invalidate_caches();
        Ok(NDet::single(Atom::sym("True")))
    });
}
fn name_arg(atom: &Atom, what: &str) -> Result<String, String> {
    match atom {
        Atom::Sym(s) => Ok(s.as_str().to_string()),
        Atom::Str(s) => Ok(s.as_ref().to_string()),
        other => Err(format!("{what} expects symbol or string, got {other:?}")),
    }
}
pub fn register_imported_prolog_function(funcs: &FnTable, functor: &str, arity: u8) {
    let functor_name = functor.to_string();
    funcs.insert_native(functor, arity, move |call_args, _| {
        let mut atoms = match ops::call_function(&functor_name, call_args) {
            Err(PrologError::Exception(msg)) => return Err(msg),
            Err(e) => return Err(e.to_string()),
            Ok(atoms) => atoms,
        };
        Ok(match atoms.len() {
            0 => NDet::empty(),
            1 => NDet::single(atoms.pop().unwrap()),
            _ => NDet::stream(atoms.into_iter()),
        })
    });
    funcs.invalidate_caches();
}
pub fn try_resolve_imported_prolog_function(funcs: &FnTable, name: &str, arity: u8) -> bool {
    if !funcs.imported_prolog_funcs.read().unwrap().contains(name) { return false; }
    if !ops::current_arities(name).is_ok_and(|a| a.contains(&(arity as usize + 1))) { return false; }
    register_imported_prolog_function(funcs, name, arity);
    true
}
