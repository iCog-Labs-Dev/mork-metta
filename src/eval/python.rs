/// Python bridge via PyO3.
///
/// Implements `(py-call ...)` and `(py-eval ...)` for calling Python
/// functions and evaluating Python expressions from MeTTa.
///
/// Opaque Python values are stored as `Atom::Gnd(PyObjectGrounded)` —
/// no conversion cost for complex objects.
use crate::atom::{Atom, Grounded};
use crate::Env;
use std::sync::Arc;

/// Evaluate `(py-call expr)` — single-expression Python call.
pub(crate) fn eval_py_call(
    args: &[crate::parser::Expr],
    env: &Env,
    _funcs: &crate::func::FnTable,
) -> Result<crate::func::NDet, String> {
    if args.len() != 1 {
        return Err(format!(
            "py-call: expected 1 arg (a Python expression), got {}",
            args.len()
        ));
    }
    #[cfg(feature = "python-bridge")]
    {
        use pyo3::prelude::*;
        use pyo3::types::PyAnyMethods;
        Python::with_gil(|py| {
            let py_obj = expr_to_py(&args[0], env, _funcs, py)?;
            let result = py_obj
                .call0()
                .map_err(|e| format!("py-call: {}", e))?;
            Ok(crate::func::NDet::single(atom_from_py(&result)))
        })
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        Err(
            "py-call: python-bridge feature not enabled. Rebuild with --features python-bridge"
                .into(),
        )
    }
}

/// Evaluate `(py-eval "code")` — evaluate arbitrary Python code string.
pub(crate) fn eval_py_eval(
    args: &[crate::parser::Expr],
    _env: &Env,
    _funcs: &crate::func::FnTable,
) -> Result<crate::func::NDet, String> {
    if args.len() != 1 {
        return Err(format!(
            "py-eval: expected 1 arg (a string of Python code), got {}",
            args.len()
        ));
    }
    let code = match &args[0] {
        crate::parser::Expr::Str(s) => s.clone(),
        other => {
            return Err(format!("py-eval: expected a string, got {:?}", other))
        }
    };
    #[cfg(feature = "python-bridge")]
    {
        use pyo3::prelude::*;
        Python::with_gil(|py| {
            let c_code = std::ffi::CString::new(code)
                .map_err(|e| format!("py-eval: invalid code string: {}", e))?;
            let result = py
                .eval(&c_code, None, None)
                .map_err(|e| format!("py-eval: error: {}", e))?;
            Ok(crate::func::NDet::single(atom_from_py(&result)))
        })
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        Err(
            "py-eval: python-bridge feature not enabled. Rebuild with --features python-bridge"
                .into(),
        )
    }
}

/// Import a Python file as a module (from `(library ...)` import).
pub(crate) fn eval_py_import_library(file_path: &std::path::Path) -> Result<(), String> {
    #[cfg(feature = "python-bridge")]
    {
        use pyo3::prelude::*;
        use pyo3::types::PyAnyMethods;
        Python::with_gil(|py| -> Result<(), String> {
            let dir = file_path
                .parent()
                .unwrap_or(std::path::Path::new("."))
                .canonicalize()
                .map_err(|e| format!("py-import: cannot resolve directory: {}", e))?;
            let dir_str = dir.to_string_lossy().to_string();
            let stem = file_path
                .file_stem()
                .and_then(|s| s.to_str())
                .ok_or_else(|| format!("py-import: invalid file name: {}", file_path.display()))?;

            let sys = py
                .import("sys")
                .map_err(|e| format!("py-import: cannot import sys: {}", e))?;
            let sys_path = sys
                .getattr("path")
                .map_err(|e| format!("py-import: cannot get sys.path: {}", e))?;
            sys_path
                .call_method1("insert", (0, dir_str))
                .map_err(|e| format!("py-import: failed to add path: {}", e))?;
            py.import(stem).map_err(|e| {
                format!(
                    "py-import: cannot import '{}' from {}: {}",
                    stem,
                    dir.display(),
                    e
                )
            })?;
            Ok(())
        })
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        let _ = file_path;
        Err(
            "py-import: python-bridge feature not enabled. Rebuild with --features python-bridge"
                .into(),
        )
    }
}

// ---------------------------------------------------------------------------
// PyO3 implementation (feature-gated)
// ---------------------------------------------------------------------------

/// Convert a Python object to a MeTTa Atom.
///
/// Simple types (int, float, str, bool, None, list, tuple, dict) are converted
/// eagerly. Opaque Python objects become `Atom::Gnd(PyObjectGrounded)` with no
/// further conversion — they stay as Python references.
#[cfg(feature = "python-bridge")]
fn atom_from_py(obj: &pyo3::Bound<'_, pyo3::types::PyAny>) -> Atom {
    use pyo3::types::PyAnyMethods;
    use pyo3::types::PyListMethods;
    use pyo3::types::PyTupleMethods;
    use pyo3::types::PyDictMethods;

    // None → empty list
    if obj.is_none() {
        return Atom::expr(Vec::<Atom>::new());
    }

    // Bool → symbol (must be before int — bool is subclass of int in Python)
    if let Ok(b) = obj.extract::<bool>() {
        return Atom::sym(if b { "true" } else { "false" });
    }

    // Integer
    if let Ok(i) = obj.extract::<i64>() {
        return Atom::num(i as i128);
    }
    if let Ok(i) = obj.extract::<i128>() {
        return Atom::num(i);
    }

    // Float → decimal
    if let Ok(f) = obj.extract::<f64>() {
        if let Ok(a) = Atom::decimal(&f.to_string()) {
            return a;
        }
    }

    // String
    if let Ok(s) = obj.extract::<String>() {
        return Atom::str_val(&s);
    }

    // List → Expr
    if let Ok(list) = obj.downcast::<pyo3::types::PyList>() {
        let items: Vec<Atom> = list.iter().map(|item| atom_from_py(&item)).collect();
        return Atom::expr(items);
    }

    // Tuple → Expr
    if let Ok(tuple) = obj.downcast::<pyo3::types::PyTuple>() {
        let items: Vec<Atom> = tuple.iter().map(|item| atom_from_py(&item)).collect();
        return Atom::expr(items);
    }

    // Dict → Expr list of (key val) pairs
    if let Ok(d) = obj.downcast::<pyo3::types::PyDict>() {
        let mut items = Vec::new();
        for (k, v) in d.iter() {
            items.push(Atom::expr(vec![atom_from_py(&k), atom_from_py(&v)]));
        }
        return Atom::expr(items);
    }

    // Opaque → Gnd
    Atom::Gnd(Arc::new(PyObjectGrounded {
        obj: obj.clone().unbind(),
    }))
}

/// Wraps a Python object reference as a MeTTa `Grounded` value.
#[cfg(feature = "python-bridge")]
struct PyObjectGrounded {
    obj: pyo3::Py<pyo3::types::PyAny>,
}

#[cfg(feature = "python-bridge")]
impl std::fmt::Debug for PyObjectGrounded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PyObject({:p})", self.obj.as_ptr())
    }
}

#[cfg(feature = "python-bridge")]
impl Grounded for PyObjectGrounded {
    fn display_metta(&self) -> String {
        use pyo3::types::PyAnyMethods;
        use pyo3::types::PyStringMethods;
        pyo3::Python::with_gil(|py| {
            self.obj
                .bind(py)
                .str()
                .map(|s| s.to_string())
                .unwrap_or_else(|_| format!("<PyObject at {:p}>", self.obj.as_ptr()))
        })
    }

    fn eq_gnd(&self, other: &dyn Grounded) -> bool {
        use pyo3::types::PyAnyMethods;
        if let Some(other) = other.as_any().downcast_ref::<PyObjectGrounded>() {
            if self.obj.as_ptr() == other.obj.as_ptr() {
                return true;
            }
            pyo3::Python::with_gil(|py| {
                self.obj
                    .bind(py)
                    .eq(other.obj.bind(py))
                    .unwrap_or(false)
            })
        } else {
            false
        }
    }

    fn hash_gnd(&self) -> u64 {
        use pyo3::types::PyAnyMethods;
        pyo3::Python::with_gil(|py| self.obj.bind(py).hash().unwrap_or(0) as u64)
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

/// Convert a MeTTa Atom to a Python object.
#[cfg(feature = "python-bridge")]
fn atom_to_py<'py>(
    atom: &Atom,
    py: pyo3::Python<'py>,
) -> Result<pyo3::Bound<'py, pyo3::types::PyAny>, String> {
    use pyo3::prelude::*;
    match atom {
        Atom::Sym(s) | Atom::Str(s) => {
            let ps: pyo3::Bound<'_, pyo3::types::PyString> =
                pyo3::types::PyString::new(py, s);
            Ok(ps.into_any())
        }
        Atom::Num(n) => match n {
            crate::atom::Numeric::Int(i) => {
                let is = i.to_string();
                if let Ok(val) = is.parse::<i64>() {
                    Ok(val.into_py(py).into_bound(py))
                } else {
                    Ok(is.into_py(py).into_bound(py))
                }
            }
            crate::atom::Numeric::Dec(d) => {
                let ds = d.to_string();
                if let Ok(val) = ds.parse::<f64>() {
                    Ok(val.into_py(py).into_bound(py))
                } else {
                    Ok(ds.into_py(py).into_bound(py))
                }
            }
        },
        Atom::Expr(items) => {
            use pyo3::types::PyListMethods;
            let list = pyo3::types::PyList::empty(py);
            for item in items.iter() {
                list.append(atom_to_py(item, py)?)
                    .map_err(|e| e.to_string())?;
            }
            Ok(list.into_any())
        }
        Atom::Closure(c) => {
            let param_strs: Vec<String> = c.params.iter().map(|p| p.to_string()).collect();
            let s = format!("(|-> ({}) {})", param_strs.join(" "), c.body.to_string());
            let ps: pyo3::Bound<'_, pyo3::types::PyString> =
                pyo3::types::PyString::new(py, &s);
            Ok(ps.into_any())
        }
        Atom::Gnd(g) => {
            // Extract the Python object directly if it's a PyObjectGrounded.
            if let Some(py_obj) = g.as_any().downcast_ref::<PyObjectGrounded>() {
                Ok(py_obj.obj.bind(py).clone().into_any())
            } else {
                // Fallback: display string
                let ps: pyo3::Bound<'_, pyo3::types::PyString> =
                    pyo3::types::PyString::new(py, &g.display_metta());
                Ok(ps.into_any())
            }
        }
    }
}

/// Convert a MeTTa expression (parser Expr) to a Python object.
///
/// Symbols are resolved as Python dotted names. `$var` looks up the
/// MeTTa env. Lists become Python function calls or nested forms.
#[cfg(feature = "python-bridge")]
fn expr_to_py<'py>(
    expr: &crate::parser::Expr,
    env: &Env,
    funcs: &crate::func::FnTable,
    py: pyo3::Python<'py>,
) -> Result<pyo3::Bound<'py, pyo3::types::PyAny>, String> {
    use pyo3::prelude::*;
    use pyo3::types::PyAnyMethods;
    match expr {
        crate::parser::Expr::Symbol(name) => {
            if name.starts_with('$') {
                let val = env.get(name).ok_or_else(|| {
                    format!("py-call: undefined variable '{}'", name)
                })?;
                return atom_to_py(&val, py);
            }
            resolve_python_name(name, py)
        }
        crate::parser::Expr::Str(s) => {
            let ps: pyo3::Bound<'_, pyo3::types::PyString> =
                pyo3::types::PyString::new(py, s);
            Ok(ps.into_any())
        }
        crate::parser::Expr::Number(n) => match n {
            crate::atom::Numeric::Int(i) => {
                let is = i.to_string();
                if let Ok(val) = is.parse::<i64>() {
                    Ok(val.into_py(py).into_bound(py))
                } else {
                    Ok(is.into_py(py).into_bound(py))
                }
            }
            crate::atom::Numeric::Dec(d) => {
                let ds = d.to_string();
                if let Ok(val) = ds.parse::<f64>() {
                    Ok(val.into_py(py).into_bound(py))
                } else {
                    Ok(ds.into_py(py).into_bound(py))
                }
            }
        },
        crate::parser::Expr::List(items) => {
            if items.is_empty() {
                let empty_code = std::ffi::CString::new("()")
                    .map_err(|e| format!("py-call: invalid empty tuple code: {}", e))?;
                Ok(py
                    .eval(&empty_code, None, None)
                    .map_err(|e| format!("py-call: cannot create empty tuple: {}", e))?)
            } else {
                match &items[0] {
                    crate::parser::Expr::Symbol(head) if head == "py-call" => {
                        if items.len() < 2 {
                            return Err("py-call: nested py-call needs an argument".into());
                        }
                        if items.len() == 2 {
                            expr_to_py(&items[1], env, funcs, py)
                        } else {
                            let inner =
                                crate::parser::Expr::List(items[1..].to_vec().into());
                            expr_to_py(&inner, env, funcs, py)
                        }
                    }
                    crate::parser::Expr::Symbol(head) if head == "py-eval" => {
                        if items.len() < 2 {
                            return Err("py-call: nested py-eval needs an argument".into());
                        }
                        let code = match &items[1] {
                            crate::parser::Expr::Str(s) => s.clone(),
                            other => {
                                return Err(format!(
                                    "py-call: nested py-eval expects a string, got {:?}",
                                    other
                                ))
                            }
                        };
                        let c_code = std::ffi::CString::new(code)
                            .map_err(|e| format!("py-call: invalid code in nested py-eval: {}", e))?;
                        let result = py.eval(&c_code, None, None).map_err(|e| {
                            format!("py-call: nested py-eval failed: {}", e)
                        })?;
                        Ok(result)
                    }
                    _ => {
                        // Normal function call: (func arg1 arg2 ...)
                        let func_obj = if let crate::parser::Expr::Str(name) = &items[0] {
                            resolve_python_name(name, py)?
                        } else {
                            expr_to_py(&items[0], env, funcs, py)?
                        };
                        let mut args: Vec<pyo3::Bound<'_, pyo3::types::PyAny>> = Vec::new();
                        for arg in &items[1..] {
                            let atom = crate::eval::machine::step::run_rs(
                                std::sync::Arc::new(arg.clone()),
                                env.clone(),
                                funcs,
                                &mut None,
                            )
                            .map_err(|e| format!("py-call: failed to evaluate arg: {}", e))?
                            .into_iter()
                            .next()
                            .map(|(a, _)| a)
                            .unwrap_or_else(|| crate::atom::Atom::sym("()"));
                            args.push(atom_to_py(&atom, py)?);
                        }
                        let args_tuple = pyo3::types::PyTuple::new(py, args.as_slice())
                            .map_err(|e| format!("py-call: failed to create args tuple: {}", e))?;
                        func_obj
                            .call1(&args_tuple)
                            .map_err(|e| format!("py-call: call failed: {}", e))
                    }
                }
            }
        }
    }
}

/// Resolve a dotted Python name (e.g. `"operator.add"`, `"builtins.index"`).
#[cfg(feature = "python-bridge")]
fn resolve_python_name<'py>(
    name: &str,
    py: pyo3::Python<'py>,
) -> Result<pyo3::Bound<'py, pyo3::types::PyAny>, String> {
    use pyo3::types::PyAnyMethods;
    let parts: Vec<&str> = name.split('.').collect();
    if parts.is_empty() {
        return Err(format!("py-call: empty name"));
    }

    // Try builtins first for the first segment
    let builtins = py
        .import("builtins")
        .map_err(|e| format!("py-call: cannot import builtins: {}", e))?;

    let first = parts[0];
    let obj = if let Ok(b) = builtins.getattr(first) {
        b
    } else {
        // Not a builtin — try as a top-level import
        let mod_obj = py
            .import(first)
            .map_err(|e| {
                format!(
                    "py-call: cannot resolve '{}' (not a builtin or module): {}",
                    first, e
                )
            })?;
        mod_obj.into_any()
    };

    // Walk the remaining dotted path
    let mut current = obj;
    for part in &parts[1..] {
        current = current
            .getattr(*part)
            .map_err(|e| {
                format!("py-call: cannot resolve '{}': {}", parts[..].join("."), e)
            })?;
    }
    Ok(current.into_any())
}
