/// Python bridge via PyO3.
///
/// Implements `(py-call ...)` and `(py-eval ...)` for calling Python
/// functions and evaluating Python expressions from MeTTa.
///
/// # `py-call` — single-expression convention
///
/// `(py-call expr)` takes ONE argument — a Python expression tree:
///
/// | MeTTa | Python |
/// |-------|--------|
/// | `(py-call (dict))` | `dict()` |
/// | `(py-call (operator.add $a $b))` | `operator.add(a, b)` |
/// | `(py-call (getattr $obj "attr"))` | `getattr(obj, "attr")` |
/// | `(py-call (str $x))` | `str(x)` |
///
/// Symbol heads are resolved as Python dotted names (try builtins first,
/// then import). `$var` is looked up in the MeTTa environment.
/// Nested `(py-call ...)` inside an expression is handled recursively.
///
/// # `py-eval`
///
/// `(py-eval "python code")` evaluates arbitrary Python code and returns
/// the result as a MeTTa atom.
///
/// # `py-import-library`
///
/// Handles `(library name.py)` from the import path — adds the file's
/// directory to `sys.path` and imports the module so `py-call` can
/// resolve dotted names into it.
///
/// Requires building with `--features python-bridge`.
use crate::atom::Atom;
use crate::Env;

/// Evaluate `(py-call expr)` — single-expression Python call.
pub(crate) fn eval_py_call(
    args: &[crate::parser::Expr],
    env: &Env,
    funcs: &crate::func::FnTable,
) -> Result<crate::func::NDet, String> {
    if args.len() != 1 {
        return Err(format!(
            "py-call: expected 1 arg (a Python expression), got {}",
            args.len()
        ));
    }
    #[cfg(feature = "python-bridge")]
    {
        return eval_py_impl(&args[0], env, funcs);
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        Err("py-call: python-bridge feature not enabled. Rebuild with --features python-bridge".into())
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
            return Err(format!(
                "py-eval: expected a string, got {:?}",
                other
            ))
        }
    };
    #[cfg(feature = "python-bridge")]
    {
        return eval_py_eval_impl(&code);
    }
    #[cfg(not(feature = "python-bridge"))]
    {
        Err("py-eval: python-bridge feature not enabled. Rebuild with --features python-bridge".into())
    }
}

/// Import a Python file as a module (from `(library ...)` import).
///
/// Adds the file's directory to Python's `sys.path` and imports the module
/// so that `py-call` can resolve names into it.
pub(crate) fn eval_py_import_library(file_path: &std::path::Path) -> Result<(), String> {
    #[cfg(feature = "python-bridge")]
    {
        eval_py_import_library_impl(file_path)
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

#[cfg(feature = "python-bridge")]
fn eval_py_impl(
    expr: &crate::parser::Expr,
    env: &Env,
    funcs: &crate::func::FnTable,
) -> Result<crate::func::NDet, String> {
    use pyo3::prelude::*;
    Python::with_gil(|py| {
        let py_obj = expr_to_py(expr, env, funcs, py)?;
        let atom = py_to_atom(&py_obj)?;
        Ok(crate::func::NDet::single(atom))
    })
}

#[cfg(feature = "python-bridge")]
fn eval_py_eval_impl(code: &str) -> Result<crate::func::NDet, String> {
    use pyo3::prelude::*;
    Python::with_gil(|py| {
        let c_code = std::ffi::CString::new(code)
            .map_err(|e| format!("py-eval: invalid code string: {}", e))?;
        let result = py
            .eval(&c_code, None, None)
            .map_err(|e| format!("py-eval: error: {}", e))?;
        let atom = py_to_atom(&result)?;
        Ok(crate::func::NDet::single(atom))
    })
}

#[cfg(feature = "python-bridge")]
fn eval_py_import_library_impl(file_path: &std::path::Path) -> Result<(), String> {
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

        // Add directory to sys.path so the module is importable
        let sys = py
            .import("sys")
            .map_err(|e| format!("py-import: cannot import sys: {}", e))?;
        let sys_path = sys
            .getattr("path")
            .map_err(|e| format!("py-import: cannot get sys.path: {}", e))?;
        sys_path
            .call_method1("insert", (0, dir_str.clone()))
            .map_err(|e| format!("py-import: failed to add path: {}", e))?;

        // Import the module so py-call can resolve dotted names into it
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

// ---------------------------------------------------------------------------
// Python-Object to/from MeTTa-Atom conversion
// ---------------------------------------------------------------------------

/// Convert a MeTTa expression to a Python object.
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
                // Look up variable in environment (Env::get expects $ prefix)
                let val = env.get(name).ok_or_else(|| {
                    format!("py-call: undefined variable '{}'", name)
                })?;
                return atom_to_py(&val, py);
            }
            // Try to resolve as a Python dotted name
            resolve_python_name(name, py)
        }
        crate::parser::Expr::Str(s) => {
            let py_s: pyo3::Bound<'_, pyo3::types::PyString> = pyo3::types::PyString::new(py, s);
            Ok(py_s.into_any())
        }
        crate::parser::Expr::Number(n) => {
            match n {
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
            }
        }
        crate::parser::Expr::List(items) => {
            if items.is_empty() {
                // Create empty Python tuple via py.eval
                let empty_code = std::ffi::CString::new("()")
                    .map_err(|e| format!("py-call: invalid empty tuple code: {}", e))?;
                Ok(py
                    .eval(&empty_code, None, None)
                    .map_err(|e| format!("py-call: cannot create empty tuple: {}", e))?)
            } else {
                // Check head for nested forms
                match &items[0] {
                    crate::parser::Expr::Symbol(head) if head == "py-call" => {
                        // Nested py-call: evaluate it recursively.
                        // (py-call expr) takes ONE argument — pass it directly.
                        if items.len() < 2 {
                            return Err("py-call: nested py-call needs an argument".into());
                        }
                        // Single argument: evaluate directly without wrapping in List
                        if items.len() == 2 {
                            expr_to_py(&items[1], env, funcs, py)
                        } else {
                            let inner = crate::parser::Expr::List(items[1..].to_vec().into());
                            expr_to_py(&inner, env, funcs, py)
                        }
                    }
                    crate::parser::Expr::Symbol(head) if head == "py-eval" => {
                        // Nested py-eval: "code" inside a py-call expression
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
                        // A string head like ("random.random" ...) means dotted Python name.
                        let func_obj = if let crate::parser::Expr::Str(name) = &items[0] {
                            resolve_python_name(name, py)?
                        } else {
                            expr_to_py(&items[0], env, funcs, py)?
                        };
                        // Evaluate each arg as MeTTa first, then convert to Python.
                        // This handles cases like (/ $w ...) embedded in py-call args.
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
    use pyo3::prelude::*;
    use pyo3::types::PyAnyMethods;

    let parts: Vec<&str> = name.split('.').collect();
    if parts.is_empty() {
        return Err("py-call: empty name".into());
    }

    let builtins = py
        .import("builtins")
        .map_err(|e| format!("py-call: failed to access builtins: {}", e))?;

    // For single-component names, try builtins first (dict, str, getattr, etc.)
    if parts.len() == 1 {
        if let Ok(obj) = builtins.getattr(parts[0]) {
            return Ok(obj);
        }
    }

    let first = parts[0];

    // First check if the module is already in sys.modules (from a previous import)
    let sys = py.import("sys").ok();
    let modules = sys.as_ref().and_then(|s| s.getattr("modules").ok());
    if let Some(mods) = modules {

        if let Ok(module) = mods.get_item(first) {
                if parts.len() == 1 {
                    return Ok(module.into_any());
                }
                let mut obj = module.into_any();
                for part in &parts[1..] {
                    obj = obj.getattr(*part).map_err(|e| {
                        format!("py-call: '{}' has no attribute '{}': {}", name, part, e)
                    })?;
                }
                return Ok(obj);
            }
    }


    // Try importing the first component as a module, then chain attributes
    if let Ok(module) = py.import(first) {
        if parts.len() == 1 {
            return Ok(module.into_any());
        }
        let mut obj = module.into_any();
        for part in &parts[1..] {
            obj = obj.getattr(*part).map_err(|e| {
                format!("py-call: '{}' has no attribute '{}': {}", name, part, e)
            })?;
        }
        return Ok(obj);
    }

    Err(format!(
        "py-call: cannot resolve Python name '{}' (not a builtin or importable module)",
        name
    ))
}

/// Convert a MeTTa Atom to a Python object.
#[cfg(feature = "python-bridge")]
fn atom_to_py<'py>(
    atom: &Atom,
    py: pyo3::Python<'py>,
) -> Result<pyo3::Bound<'py, pyo3::types::PyAny>, String> {
    use pyo3::prelude::*;
    match atom {
        Atom::Sym(s) => {
            let py_s: pyo3::Bound<'_, pyo3::types::PyString> = pyo3::types::PyString::new(py, s);
            Ok(py_s.into_any())
        }
        Atom::Str(s) => {
            let py_s: pyo3::Bound<'_, pyo3::types::PyString> = pyo3::types::PyString::new(py, s);
            Ok(py_s.into_any())
        }
        Atom::Num(n) => {
            match n {
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
            }
        }
        // For compound atoms, represent as Python string for now
        a => {
            let py_s: pyo3::Bound<'_, pyo3::types::PyString> = pyo3::types::PyString::new(py, &a.to_sexpr_string());
            Ok(py_s.into_any())
        }
    }
}

/// Convert a Python object back to a MeTTa Atom.
#[cfg(feature = "python-bridge")]
fn py_to_atom(obj: &pyo3::Bound<'_, pyo3::types::PyAny>) -> Result<Atom, String> {
    use pyo3::types::PyAnyMethods;
    use pyo3::types::PyDictMethods;
    use pyo3::types::PyListMethods;
    use pyo3::types::PyTupleMethods;
    // Try numeric types first
    if let Ok(i) = obj.extract::<i64>() {
        return Ok(Atom::num(i as i128));
    }
    if let Ok(f) = obj.extract::<f64>() {
        return Ok(Atom::decimal(&f.to_string())?);
    }
    // String
    if let Ok(s) = obj.extract::<String>() {
        return Ok(Atom::sym(&s));
    }
    // None → empty list
    if obj.is_none() {
        return Ok(Atom::expr(vec![]));
    }
    // List / Tuple
    if let Ok(tuple) = obj.downcast::<pyo3::types::PyTuple>() {
        let mut items = Vec::new();
        for item in tuple.iter() {
            items.push(py_to_atom(&item)?);
        }
        return Ok(Atom::expr(items));
    }
    if let Ok(list) = obj.downcast::<pyo3::types::PyList>() {
        let mut items = Vec::new();
        for item in list.iter() {
            items.push(py_to_atom(&item)?);
        }
        return Ok(Atom::expr(items));
    }
    // Dict → list of pairs
    if let Ok(d) = obj.downcast::<pyo3::types::PyDict>() {
        let mut items = Vec::new();
        for (k, v) in d.iter() {
            let key_atom = py_to_atom(&k)?;
            let val_atom = py_to_atom(&v)?;
            items.push(Atom::expr(vec![key_atom, val_atom]));
        }
        return Ok(Atom::expr(items));
    }
    // Fallback: repr
    let repr = obj.repr().map_err(|e| format!("py-to-atom: repr failed: {}", e))?;
    let s: String = repr.extract().map_err(|e| {
        format!("py-to-atom: repr extraction failed: {}", e)
    })?;
    Ok(Atom::sym(&s))
}
