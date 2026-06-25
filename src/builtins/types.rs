//! Builtins for structural and declaration-backed type inspection.

use crate::atom::Atom;
use crate::func::{FnTable, NDet};

fn expect(args: &[Atom], n: usize, name: &str) -> Result<(), String> {
    crate::builtins::arithmetic::expect_n_args(args, n, name)
}

fn bool_atom(value: bool) -> Atom {
    crate::builtins::boolean::bool_atom(value)
}

fn direct_type_decl(subject: &Atom, table: &FnTable) -> Result<Option<Atom>, String> {
    let self_ref = Atom::sym("&self");
    let atoms = table.with_resolved_space(&self_ref, |space| Ok(space.get_atoms()))?;
    for atom in atoms {
        let Atom::Expr(items) = atom else {
            continue;
        };
        if items.len() != 3 || items[0] != Atom::sym(":") {
            continue;
        }
        if items[1] == *subject {
            return Ok(Some(items[2].clone()));
        }
    }
    Ok(None)
}

fn function_type_decl(head: &Atom, arity: usize, table: &FnTable) -> Result<Vec<Vec<Atom>>, String> {
    let self_ref = Atom::sym("&self");
    let atoms = table.with_resolved_space(&self_ref, |space| Ok(space.get_atoms()))?;
    let mut out = Vec::new();
    for atom in atoms {
        let Atom::Expr(items) = atom else {
            continue;
        };
        if items.len() != 3 || items[0] != Atom::sym(":") || items[1] != *head {
            continue;
        }
        let Atom::Expr(sig) = &items[2] else {
            continue;
        };
        if sig.len() != arity + 2 || sig[0] != Atom::sym("->") {
            continue;
        }
        out.push(sig.iter().skip(1).cloned().collect());
    }
    Ok(out)
}

fn infer_type(atom: &Atom, table: &FnTable) -> Result<Atom, String> {
    match atom {
        Atom::Num(_) => return Ok(Atom::sym("Number")),
        Atom::Sym(s) if s.as_ref() == "true" || s.as_ref() == "false" => return Ok(Atom::sym("Bool")),
        Atom::Expr(items) if !items.is_empty() => {
            if let Some(decl) = direct_type_decl(atom, table)? {
                return Ok(decl);
            }
            let head = &items[0];
            let args = &items[1..];
            for sig in function_type_decl(head, args.len(), table)? {
                let (expected_args, result_ty) = sig.split_at(sig.len() - 1);
                let mut matched = true;
                for (arg, expected) in args.iter().zip(expected_args.iter()) {
                    if infer_type(arg, table)? != *expected {
                        matched = false;
                        break;
                    }
                }
                if matched {
                    return Ok(result_ty[0].clone());
                }
            }
            Ok(Atom::Expr(crate::atom::expr_data([
                Atom::sym("get-type"),
                atom.clone(),
            ])))
        }
        _ => {
            if let Some(decl) = direct_type_decl(atom, table)? {
                Ok(decl)
            } else {
                Ok(Atom::Expr(crate::atom::expr_data([
                    Atom::sym("get-type"),
                    atom.clone(),
                ])))
            }
        }
    }
}

/// Register type-inspection builtins.
pub fn register_type_builtins(funcs: &FnTable) {
    funcs.insert_native("is-var", 1, |args, _| {
        expect(args, 1, "is-var")?;
        let is_var = matches!(&args[0], Atom::Sym(symbol) if symbol.starts_with('$'));
        Ok(NDet::single(bool_atom(is_var)))
    });
    funcs.mark_pure("is-var", 1);

    funcs.insert_native("is-expr", 1, |args, _| {
        expect(args, 1, "is-expr")?;
        Ok(NDet::single(bool_atom(matches!(&args[0], Atom::Expr(_)))))
    });
    funcs.mark_pure("is-expr", 1);

    funcs.insert_native("is-space", 1, |args, _| {
        expect(args, 1, "is-space")?;
        let is_space = matches!(&args[0], Atom::Sym(symbol) if symbol.starts_with('&'));
        Ok(NDet::single(bool_atom(is_space)))
    });
    funcs.mark_pure("is-space", 1);

    funcs.insert_native("get-type", 1, |args, table| {
        expect(args, 1, "get-type")?;
        Ok(NDet::single(infer_type(&args[0], table)?))
    });

    funcs.insert_native("get-metatype", 1, |args, _| {
        expect(args, 1, "get-metatype")?;
        let kind = match &args[0] {
            Atom::Sym(symbol) if symbol.starts_with('&') => "Space",
            Atom::Sym(symbol) if symbol.starts_with('$') => "Variable",
            Atom::Sym(_) => "Symbol",
            Atom::Str(_) => "String",
            Atom::Num(_) => "Number",
            Atom::Expr(_) => "Expression",
            Atom::Closure(_) => "Grounded",
            Atom::Gnd(_) => "Grounded",
        };
        Ok(NDet::single(Atom::sym(kind)))
    });
    funcs.mark_pure("get-metatype", 1);
}
