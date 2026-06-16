/// Python bridge via PyO3.
///
/// Evaluates `(py-call module func arg1 arg2 ...)` by calling a Python
/// function from the specified module with the given arguments.
///
/// Requires building with `--features python-bridge`.
use crate::atom::Atom;
use crate::env::Env;
use crate::eval_parts::core::eval_scope;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;

/// Evaluate `(py-call module func arg1 arg2 ...)`.
///
/// Calls a Python function from a module with the given arguments.
/// - `module` — Python module name (string)
/// - `func` — function name within the module (string)
/// - `arg1 arg2 ...` — arguments converted to Python objects
///
/// Returns the Python result converted back to a MeTTa atom.
/// Requires building with `--features python-bridge`.
pub(crate) fn eval_py_call(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() < 2 {
        return Err(format!(
            "py-call: expected at least (module func), got {} args",
            args.len()
        ));
    }
    #[cfg(feature = "python-bridge")]
    {
        return eval_py_call_impl(args, env, funcs);
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        let _ = env;
        let _ = funcs;
        Err(
            "py-call: python-bridge feature not enabled. Rebuild with --features python-bridge"
                .into(),
        )
    }
}

#[cfg(feature = "python-bridge")]
fn eval_py_call_impl(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    use pyo3::prelude::*;

    /// Convert a MeTTa atom to a Python object.
    fn atom_to_py<'py>(atom: &Atom, py: Python<'py>) -> Result<Bound<'py, PyAny>, String> {
        match atom {
            Atom::Num(n) => {
                let obj = n
                    .into_pyobject(py)
                    .map_err(|e| format!("py-call: failed to convert number {}: {}", n, e))?;
                Ok(obj.into_any())
            }
            Atom::Sym(s) => {
                let py_str = pyo3::types::PyString::new(py, &**s);
                Ok(py_str.into_any())
            }
            Atom::Expr(items) => {
                let list = pyo3::types::PyList::empty(py);
                for item in items {
                    let obj = atom_to_py(item, py)?;
                    list.append(obj)
                        .map_err(|e| format!("py-call: failed to build list: {}", e))?;
                }
                Ok(list.into_any())
            }
            Atom::Closure(_) => {
                let s = atom.to_sexpr_string();
                let py_str = pyo3::types::PyString::new(py, &s);
                Ok(py_str.into_any())
            }
        }
    }

    /// Convert a Python object back to a MeTTa atom.
    fn py_to_atom(obj: &Bound<'_, PyAny>) -> Result<Atom, String> {
        if let Ok(n) = obj.extract::<i128>() {
            return Ok(Atom::Num(n));
        }
        if let Ok(f) = obj.extract::<f64>() {
            let s = format!("{}", f);
            return Ok(Atom::sym(&s));
        }
        if let Ok(s) = obj.extract::<String>() {
            return Ok(Atom::sym(&s));
        }
        if let Ok(b) = obj.extract::<bool>() {
            return Ok(if b {
                Atom::sym("True")
            } else {
                Atom::sym("False")
            });
        }
        if obj.is_none() {
            return Err("py-call: Python function returned None".into());
        }
        if let Ok(list) = obj.downcast::<pyo3::types::PyList>() {
            let atoms: Result<Vec<Atom>, String> =
                list.iter().map(|item| py_to_atom(&item)).collect();
            return Ok(Atom::Expr(atoms?));
        }
        if let Ok(tup) = obj.downcast::<pyo3::types::PyTuple>() {
            let atoms: Result<Vec<Atom>, String> =
                tup.iter().map(|item| py_to_atom(&item)).collect();
            return Ok(Atom::Expr(atoms?));
        }
        let repr_val = obj
            .repr()
            .map(|r| r.to_string_lossy().to_string())
            .unwrap_or_else(|_| "<unprintable>".to_string());
        Ok(Atom::sym(&repr_val))
    }

    // Evaluate module name arg
    let mut mod_results = eval_scope(&args[0], env, funcs)?;
    let mod_atom = mod_results
        .next()
        .ok_or_else(|| "py-call: module expression produced no results".to_string())?;
    let mod_name = match &mod_atom {
        Atom::Sym(s) => s.trim_matches('"').to_string(),
        other => {
            return Err(format!(
                "py-call: module must be a symbol, got {}",
                other.to_sexpr_string()
            ));
        }
    };

    // Evaluate function name arg
    let mut func_results = eval_scope(&args[1], env, funcs)?;
    let func_atom = func_results
        .next()
        .ok_or_else(|| "py-call: function expression produced no results".to_string())?;
    let func_name = match &func_atom {
        Atom::Sym(s) => s.trim_matches('"').to_string(),
        other => {
            return Err(format!(
                "py-call: function must be a symbol, got {}",
                other.to_sexpr_string()
            ));
        }
    };

    // Evaluate remaining args
    let mut py_args: Vec<Atom> = Vec::with_capacity(args.len().saturating_sub(2));
    for arg in &args[2..] {
        let mut arg_results = eval_scope(arg, env, funcs)?;
        let arg_atom = arg_results
            .next()
            .ok_or_else(|| format!("py-call: argument expression produced no results"))?;
        py_args.push(arg_atom);
    }

    // Execute Python call (lazy init — auto-initialize handles it)
    Python::with_gil(|py| {
        let module = py
            .import(AsRef::<str>::as_ref(&mod_name))
            .map_err(|e| format!("py-call: cannot import module '{}': {}", mod_name, e))?;
        let func = module
            .getattr(AsRef::<str>::as_ref(&func_name))
            .map_err(|e| {
                format!(
                    "py-call: module '{}' has no function '{}': {}",
                    mod_name, func_name, e
                )
            })?;
        let py_objs: Result<Vec<Bound<'_, PyAny>>, String> =
            py_args.iter().map(|a| atom_to_py(a, py)).collect();
        let py_objs = py_objs?;
        let args_tuple = pyo3::types::PyTuple::new(py, &py_objs)
            .map_err(|e| format!("py-call: failed to build args tuple: {}", e))?;
        let result = func
            .call(&args_tuple, None)
            .map_err(|e| format!("py-call: error calling {}.{}: {}", mod_name, func_name, e))?;
        let atom = py_to_atom(&result)?;
        Ok(NDet::single(atom))
    })
}
