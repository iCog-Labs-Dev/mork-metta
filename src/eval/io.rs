/// I/O and file operations for the evaluator.
///
/// Provides file loading (streaming form-by-form), import resolution,
/// printing, line reading, and Import-RS plugin loading.
///
/// # Fast bulk loader
///
/// `load_metta_file` memory-maps the file (zero heap copy, OS pages on demand)
/// then splits it into rayon chunks for parallel parse. Pure data forms are
/// batch-inserted with one write-lock and one `bump_memo_stamp` at the end.
/// Definition / runnable forms still use the sequential slow path.
use crate::atom::{Atom, expr_data};
use crate::env::Env;
use crate::eval::runtime::eval_scope;
use crate::eval::{
    machine::budget::{ResultSet, plain},
    runtime::eval_with_state,
};
use crate::func::{FnTable, NDet};
use crate::parser::{Expr, TopForm, atom_to_expr, expr_to_atom, parse_atom_bytes, parse_forms};
#[cfg(feature = "plugins")]
use crate::plugin::Plugin;
use crate::space::mutate::{add_atom, add_atoms_bulk};
use rayon::prelude::*;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

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
    let space_ref = space_results
        .next()
        .ok_or_else(|| "import!: space expression produced no results".to_string())?;
    // Extract path string
    let path_str = match &args[1] {
        Expr::Symbol(s) | Expr::Str(s) => s.clone(),
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
    let result = load_metta_file(&resolved, &space_ref, env, funcs);
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
    let plugin = Plugin::new(&plugin_path)
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

/// Load a `.metta` file using memory-mapped I/O for 50GB+ scale.
///
/// # Fast path (pure data files)
/// Uses `memmap2` — zero heap copy, the OS pages in only what's accessed.
/// Scans byte offsets of all top-level forms, then parses them in parallel
/// with rayon. All parsed `Atom`s are bulk-inserted with a single write-lock
/// and a single `bump_memo_stamp` at the end.
///
/// # Slow path (definitions / runnables)
/// Any form starting with `=` or prefixed `!` falls through to the sequential
/// `process_form` path so the fn_cache is populated correctly.
pub fn load_metta_file(
    path: &Path,
    space_ref: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Vec<Atom>, String> {
    let file = std::fs::File::open(path)
        .map_err(|e| format!("cannot open '{}': {}", path.display(), e))?;

    // ponytail: mmap — OS pages on demand, no 50GB heap copy
    // SAFETY: the mmap lives for the duration of this function; we don't mutate it.
    let mmap = unsafe { memmap2::Mmap::map(&file) }
        .map_err(|e| format!("mmap '{}': {}", path.display(), e))?;
    let bytes: &[u8] = &mmap;
    let n = bytes.len();

    // ── Pass 1: scan form boundaries (sequential, byte-scan only) ───────────
    // Collect (start, end, is_bang, start_line) for every top-level form.
    struct FormSpan {
        start: usize,
        end: usize,
        is_bang: bool,
        start_line: usize,
    }
    let mut spans: Vec<FormSpan> = Vec::new();
    let mut pos = 0usize;
    let mut line_no = 1usize;

    while pos < n {
        skip_file_ws(bytes, &mut pos, &mut line_no);
        if pos >= n {
            break;
        }

        let saw_bang = bytes[pos] == b'!';
        if saw_bang {
            pos += 1;
            skip_file_ws(bytes, &mut pos, &mut line_no);
        }
        if pos >= n {
            break;
        }

        if bytes[pos] != b'(' {
            return Err(format!(
                "expected '(' in '{}' at line {}, found '{}'",
                path.display(),
                line_no,
                bytes[pos] as char
            ));
        }

        let start_line = line_no;
        let form_start = pos;
        let mut depth: i32 = 0;

        while pos < n {
            match bytes[pos] {
                b'\n' => {
                    line_no += 1;
                    pos += 1;
                }
                b';' => {
                    while pos < n && bytes[pos] != b'\n' {
                        pos += 1;
                    }
                }
                b'"' => {
                    pos += 1;
                    while pos < n {
                        match bytes[pos] {
                            b'\\' => pos += 2,
                            b'"' => {
                                pos += 1;
                                break;
                            }
                            b'\n' => {
                                line_no += 1;
                                pos += 1;
                            }
                            _ => pos += 1,
                        }
                    }
                }
                b'(' => {
                    depth += 1;
                    pos += 1;
                }
                b')' => {
                    depth -= 1;
                    pos += 1;
                    if depth == 0 {
                        break;
                    }
                    if depth < 0 {
                        return Err(format!(
                            "unmatched ')' in '{}' at line {}",
                            path.display(),
                            line_no
                        ));
                    }
                }
                _ => pos += 1,
            }
        }
        if depth != 0 {
            return Err(format!(
                "unclosed '(' in '{}' at line {}",
                path.display(),
                start_line
            ));
        }
        spans.push(FormSpan {
            start: form_start,
            end: pos,
            is_bang: saw_bang,
            start_line,
        });
    }

    // ── Pass 2: split into data-only vs slow forms ──────────────────────────
    // Data forms (no `=`, no `!`) are parsed in parallel; others sequential.
    let mut slow_indices: Vec<usize> = Vec::new();
    let mut data_indices: Vec<usize> = Vec::new();
    for (i, s) in spans.iter().enumerate() {
        if !s.is_bang && is_data_form(bytes, s.start) {
            data_indices.push(i);
        } else {
            slow_indices.push(i);
        }
    }

    // ── Pass 3: parallel parse of data forms ────────────────────────────────
    // Each rayon thread gets its own slice; all produce Atoms independently.
    // We need the bytes as a shared ref across threads — mmap is read-only.
    // SAFETY: bytes is a shared read-only slice from the mmap; no writes occur.
    let bytes_ptr = bytes.as_ptr() as usize; // send pointer across rayon boundary
    let bytes_len = bytes.len();

    let data_atoms: Vec<Result<Atom, (usize, String)>> = data_indices
        .par_iter()
        .map(|&i| {
            let s = &spans[i];
            // Reconstruct the slice per-thread.
            // SAFETY: read-only, mmap lives for function scope, rayon scope is nested.
            let bytes_slice =
                unsafe { std::slice::from_raw_parts(bytes_ptr as *const u8, bytes_len) };
            let snippet = std::str::from_utf8(&bytes_slice[s.start..s.end])
                .map_err(|e| (s.start_line, e.to_string()))?;
            let mut local_pos = 0usize;
            let mut local_line = s.start_line;
            parse_atom_bytes(snippet, &mut local_pos, &mut local_line)
                .map_err(|e| (s.start_line, e))
        })
        .collect();

    // Collect results, propagate errors
    let mut bulk_atoms: Vec<Atom> = Vec::with_capacity(data_atoms.len());
    for r in data_atoms {
        match r {
            Ok(atom) => bulk_atoms.push(atom),
            Err((line, msg)) => {
                return Err(format!(
                    "{} (in '{}' near line {})",
                    msg,
                    path.display(),
                    line
                ));
            }
        }
    }

    // ── Pass 4: bulk insert data atoms (single lock + single memo bump) ──────
    if !bulk_atoms.is_empty() {
        add_atoms_bulk(funcs, space_ref, &bulk_atoms)?;
    }

    // ── Pass 5: sequential slow path for defs / runnables ───────────────────
    let mut results: Vec<Atom> = Vec::new();
    // Re-parse content as str for slow path (these are rare: only `=` / `!` forms).
    // We re-borrow from mmap — still no copy.
    let content = std::str::from_utf8(bytes)
        .map_err(|e| format!("UTF-8 error in '{}': {}", path.display(), e))?;

    for i in slow_indices {
        let s = &spans[i];
        let form_str = &content[s.start..s.end];
        if let Some(result) = process_form(form_str, s.is_bang, space_ref, env, funcs)
            .map_err(|e| format!("{} (in '{}' near line {})", e, path.display(), s.start_line))?
        {
            results.push(result);
        }
    }

    Ok(results)
}

/// Skip ASCII whitespace and `;` line-comments, tracking line numbers.
fn skip_file_ws(bytes: &[u8], pos: &mut usize, line_no: &mut usize) {
    loop {
        while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
            if bytes[*pos] == b'\n' {
                *line_no += 1;
            }
            *pos += 1;
        }
        if *pos < bytes.len() && bytes[*pos] == b';' {
            while *pos < bytes.len() && bytes[*pos] != b'\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

/// True when the form at `pos` (which is `(`) is a data fact safe for the
/// fast parse path — i.e., the first token inside is not a standalone `=`.
fn is_data_form(bytes: &[u8], pos: usize) -> bool {
    let mut i = pos + 1; // skip '('
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i >= bytes.len() || bytes[i] == b')' {
        return true; // empty form
    }
    if bytes[i] != b'=' {
        return true; // first token not '='
    }
    // '=' found — standalone only if followed by delimiter
    let j = i + 1;
    if j >= bytes.len() {
        return false; // '=' at EOF → eq-form
    }
    let b = bytes[j];
    !(b.is_ascii_whitespace() || b == b'(' || b == b')')
}

/// Parse a single buffered form string and dispatch it.
fn process_form(
    form: &str,
    is_runnable: bool,
    space_ref: &Atom,
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
    for top_form in parse_forms(src)? {
        last = process_top_form(top_form, space_ref, env, funcs)?;
    }
    Ok(last)
}

/// Process a single top-level form: store+compile definitions, eval runnables.
pub(crate) fn process_top_form(
    form: TopForm,
    space_ref: &Atom,
    env: &Env,
    funcs: &FnTable,
) -> Result<Option<Atom>, String> {
    match form {
        TopForm::Definition(expr) => {
            let atom = expr_to_atom(&expr);
            add_atom(funcs, space_ref, &atom)?;
            Ok(None)
        }
        TopForm::Runnable(expr) => {
            // Drive the spec's 4-register machine (cost ledger + insensitive gate
            // live; unbounded budget → results identical to bare eval). This is
            // the file/CLI run path.
            let (mut results, _budget) = eval_with_state(&expr, env, funcs, None)?;
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
    match parse_forms(&wrapped) {
        Ok(forms) => {
            if let Some(TopForm::Definition(Expr::List(items))) = forms.into_iter().next() {
                if items.len() == 1 {
                    Ok(NDet::single(expr_to_atom(&items[0])))
                } else if items.is_empty() {
                    Ok(NDet::single(Atom::Expr(expr_data([]))))
                } else {
                    Ok(NDet::single(Atom::expr(
                        items
                            .into_iter()
                            .map(|e| expr_to_atom(&e))
                            .collect::<Vec<_>>(),
                    )))
                }
            } else {
                Err("readln!: Could not parse input".to_string())
            }
        }
        Err(e) => Err(format!("readln!: Parse error: {}", e)),
    }
}

/// Evaluate `println!` after its arguments have already been reduced by the machine.
pub(crate) fn finish_println(result: ResultSet) -> ResultSet {
    for (atom, _) in &result {
        eprintln!("{}", atom.to_sexpr_string());
    }
    plain(vec![Atom::sym("true")])
}
