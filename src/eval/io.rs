/// I/O and file operations for the evaluator.
///
/// Provides file loading (streaming form-by-form), import resolution,
/// printing, line reading, and Import-RS plugin loading.
///
/// # Streaming parser
///
/// `load_metta_file` uses a streaming form-by-form parser — only one
/// balanced expression is held in memory at a time, so billion-line
/// data files are safe.
use crate::atom::Atom;
use crate::env::Env;
use crate::eval::runtime::eval_scope;
use crate::func::{FnTable, NDet};
use crate::parser::{Expr, TopForm, parse_forms};
use std::path::Path;
use std::path::PathBuf;

/// Evaluate `(import! space path)` — load a MeTTa file into the space.
///
/// Path resolution order (first match wins, each tried with and without `.metta`):
///   1. As-is from CWD
///   2. Relative to the importing file's directory (`funcs.import_dir`)
///
/// Files are loaded with a streaming form-by-form parser — only one balanced
/// expression is held in memory at a time, so billion-line data files are safe.
/// `import_dir` is updated for the duration of the nested load so that imports
/// inside an imported file also resolve relative to their own location.
pub(crate) fn eval_import(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    if args.len() != 2 {
        return Err(format!(
            "import!: expected (space path), got {} args",
            args.len()
        ));
    }
    // Evaluate space reference
    let mut space_results = eval_scope(&args[0], env, funcs)?;
    let _space_ref = space_results
        .next()
        .ok_or_else(|| "import!: space expression produced no results".to_string())?;
    // Extract path string
    let path_str = match &args[1] {
        Expr::Symbol(s) => s.clone(),
        Expr::Number(_) => return Err("import!: file path must be a symbol, not a number".into()),
        Expr::List(_) => return Err("import!: file path must be a symbol, not a list".into()),
    };
    // Resolve path: CWD first, then relative to the importing file's directory.
    let import_dir = funcs.import_dir.lock().unwrap().clone();
    let resolved = resolve_import_path(&path_str, &import_dir).ok_or_else(|| {
        format!(
            "import!: cannot find '{}' (searched CWD and '{}')",
            path_str,
            import_dir.display()
        )
    })?;
    // Push the imported file's directory so nested imports resolve relative to it.
    let new_dir = resolved
        .parent()
        .unwrap_or(std::path::Path::new("."))
        .to_path_buf();
    let prev_dir = std::mem::replace(&mut *funcs.import_dir.lock().unwrap(), new_dir);
    let result = load_metta_file(&resolved, env, funcs);
    *funcs.import_dir.lock().unwrap() = prev_dir;
    result?;
    Ok(NDet::single(Atom::sym("true")))
}

/// Evaluate `(import-rs! name)` — compile and load a Rust plugin.
///
/// `name` can be a bare library name (e.g. `my_math`) or a path to a `.rs` file.
/// Search order: same dir as the importing file, then CWD, then bare path.
///
/// Requires building with `--features plugins`.
#[cfg(feature = "plugins")]
pub(crate) fn eval_import_rs(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    use std::path::Path;
    if args.len() != 1 {
        return Err(format!(
            "import-rs!: expected (name), got {} args",
            args.len()
        ));
    }
    let mut results = eval_scope(&args[0], env, funcs)?;
    let name_atom = results
        .next()
        .ok_or_else(|| "import-rs!: name expression produced no results".to_string())?;
    let name = match &name_atom {
        Atom::Sym(s) => s.as_ref().to_string(),
        other => {
            return Err(format!(
                "import-rs!: name must be a symbol, got {}",
                other.to_sexpr_string()
            ));
        }
    };

    // Search for the plugin file
    let import_dir = funcs.import_dir.lock().unwrap().clone();
    let plugin_path = find_plugin_path(&name, &import_dir)?;

    // Load and compile the plugin
    let plugin = crate::plugin::Plugin::new(&plugin_path)
        .map_err(|e| format!("import-rs!: failed to load plugin '{}': {}", name, e))?;
    plugin.register(funcs);
    Ok(NDet::single(Atom::sym("ok")))
}

/// Stub when `plugins` feature is disabled.
#[cfg(not(feature = "plugins"))]
pub(crate) fn eval_import_rs(_args: &[Expr], _env: &Env, _funcs: &FnTable) -> Result<NDet, String> {
    Err("import-rs!: plugins feature not enabled. Rebuild with --features plugins".into())
}

/// Find a plugin file by name, searching the import directory and CWD.
#[cfg(feature = "plugins")]
fn find_plugin_path(name: &str, import_dir: &Path) -> Result<PathBuf, String> {
    // Try as-is
    let path = Path::new(name);
    if path.exists() {
        return Ok(path.to_path_buf());
    }
    // Try with .rs extension
    let with_rs = Path::new(name).with_extension("rs");
    if with_rs.exists() {
        return Ok(with_rs);
    }
    // Try relative to import dir
    let rel = import_dir.join(name);
    if rel.exists() {
        return Ok(rel);
    }
    let rel_rs = import_dir.join(name).with_extension("rs");
    if rel_rs.exists() {
        return Ok(rel_rs);
    }
    Err(format!("plugin not found: {}", name))
}

/// Resolve an import path against a priority-ordered list of base directories.
///
/// Search order (first hit wins, each tried with and without `.metta`):
///   1. CWD — for absolute or CWD-relative paths
///   2. `import_dir` — relative to the importing file's own directory
///   3. Parent of CWD — for paths written relative to the project root when
///      the binary is run from a subdirectory (e.g. `metta/examples/lib.h`
///      resolves from `MORK/` when `cargo run` is invoked from `MORK/metta/`)
pub(crate) fn resolve_import_path(path_str: &str, import_dir: &Path) -> Option<PathBuf> {
    let parent_cwd = std::env::current_dir()
        .ok()
        .and_then(|d| d.parent().map(|p| p.to_path_buf()));
    let bases = std::iter::once(std::path::PathBuf::from("."))
        .chain(std::iter::once(import_dir.to_path_buf()))
        .chain(parent_cwd);
    for base in bases {
        for candidate in [
            base.join(path_str),
            base.join(format!("{}.metta", path_str)),
        ] {
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    None
}

/// Stream-load a `.metta` file: parse one balanced form at a time and process
/// it immediately, so only O(1-form) memory is used regardless of file size.
///
/// Returns the first result of the last runnable form, or `None` if the file
/// ends with a definition (matching the semantics of `load_form`).
pub fn load_metta_file(path: &Path, env: &Env, funcs: &FnTable) -> Result<Vec<Atom>, String> {
    use std::io::{BufRead, BufReader};
    let file = std::fs::File::open(path)
        .map_err(|e| format!("cannot open '{}': {}", path.display(), e))?;
    let mut form_buf = String::with_capacity(256);
    let mut depth: i32 = 0;
    let mut saw_bang = false;
    let mut results: Vec<Atom> = Vec::new();
    for (line_no, line_result) in BufReader::new(file).lines().enumerate() {
        let line = line_result.map_err(|e| {
            format!(
                "read error at line {} in '{}': {}",
                line_no + 1,
                path.display(),
                e
            )
        })?;
        for ch in line.chars() {
            match ch {
                ';' => break,
                '!' if depth == 0 => saw_bang = true,
                '(' => {
                    depth += 1;
                    form_buf.push(ch);
                }
                ')' if depth > 0 => {
                    depth -= 1;
                    form_buf.push(ch);
                    if depth == 0 {
                        if let Some(result) = process_form(&form_buf, saw_bang, env, funcs)
                            .map_err(|e| {
                                format!("{} (in '{}' near line {})", e, path.display(), line_no + 1)
                            })?
                        {
                            results.push(result);
                        }
                        form_buf.clear();
                        saw_bang = false;
                    }
                }
                ')' => {
                    return Err(format!(
                        "unmatched ')' in '{}' at line {}",
                        path.display(),
                        line_no + 1
                    ));
                }
                _ if depth > 0 => form_buf.push(ch),
                _ => {}
            }
        }
    }
    if depth != 0 {
        return Err(format!("unclosed '(' in '{}'", path.display()));
    }
    Ok(results)
}

/// Parse a single buffered form string and dispatch it.
fn process_form(
    form: &str,
    is_runnable: bool,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Atom>, String> {
    let prefixed;
    let src: &str = if is_runnable {
        prefixed = format!("!{}", form);
        &prefixed
    } else {
        form
    };
    let mut last = None;
    for top_form in crate::parser::parse_forms(src)? {
        last = process_top_form(top_form, env, funcs)?;
    }
    Ok(last)
}

/// Process a single top-level form: store+compile definitions, eval runnables.
pub(crate) fn process_top_form(
    form: TopForm,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Atom>, String> {
    match form {
        TopForm::Definition(expr) => {
            let atom = crate::parser::expr_to_atom(&expr);
            funcs
                .space
                .write()
                .unwrap()
                .add_atom(&atom)
                .map_err(|e| format!("add_atom: {}", e))?;
            if let Ok((name, clause)) = crate::compile::compile_definition(&expr) {
                // Also store the BARE HEAD atom so `match` can find premise atoms
                if let crate::parser::Expr::List(items) = &expr {
                    if items.len() == 3 {
                        let head_atom = crate::parser::expr_to_atom(&items[1]);
                        funcs.space.write().unwrap().add_atom(&head_atom)?;
                    }
                }
                // Populate fn_cache for fast concurrent dispatch
                funcs.cache_fn(&name, clause.patterns.len() as u8, clause);
            }
            Ok(None)
        }
        TopForm::Runnable(expr) => {
            // Drive the spec's 4-register machine (cost ledger + insensitive gate
            // live; unbounded budget → results identical to bare eval). This is
            // the file/CLI run path.
            let (mut results, _budget) =
                crate::eval::runtime::eval_with_state(&expr, env, funcs, None)?;
            Ok(results.next())
        }
    }
}

/// Evaluate `(readln!)` — read a line from stdin and parse it.
pub(crate) fn eval_readln(_args: &[Expr], _env: &Env, _funcs: &FnTable) -> Result<NDet, String> {
    use std::io::{self, Write};
    let mut input = String::new();
    io::stdout().flush().map_err(|e| e.to_string())?;
    io::stdin()
        .read_line(&mut input)
        .map_err(|e| e.to_string())?;
    let wrapped = format!("({})", input);
    match crate::parser::parse_forms(&wrapped) {
        Ok(forms) => {
            if let Some(crate::parser::TopForm::Definition(crate::parser::Expr::List(mut items))) =
                forms.into_iter().next()
            {
                if items.len() == 1 {
                    Ok(NDet::single(crate::parser::expr_to_atom(&items.remove(0))))
                } else if items.is_empty() {
                    Ok(NDet::single(crate::atom::Atom::Expr(vec![])))
                } else {
                    Ok(NDet::single(crate::atom::Atom::Expr(
                        items
                            .into_iter()
                            .map(|e| crate::parser::expr_to_atom(&e))
                            .collect(),
                    )))
                }
            } else {
                Err("readln!: Could not parse input".to_string())
            }
        }
        Err(e) => Err(format!("readln!: Parse error: {}", e)),
    }
}

/// Evaluate `(println! args...)` — print values to stdout (for debugging).
/// Each arg is evaluated and its results printed space-separated.
/// If a single arg is a non-empty list, its elements are printed space-separated.
pub(crate) fn eval_println(args: &[Expr], env: &Env, funcs: &FnTable) -> Result<NDet, String> {
    let mut parts = Vec::new();
    for arg in args {
        let mut results = eval_scope(arg, env, funcs)?;
        let val = results
            .next()
            .ok_or_else(|| format!("println!: argument produced no results: {:?}", arg))?;
        if let Atom::Expr(items) = &val {
            let s: Vec<String> = items.iter().map(|a| a.to_sexpr_string()).collect();
            parts.push(s.join(" "));
        } else {
            parts.push(val.to_sexpr_string());
        }
    }
    println!("{}", parts.join(" "));
    Ok(NDet::single(Atom::sym("true")))
}
