/// Dynamic plugin loading for Rust libraries in MeTTa.
///
/// The `import-rs!` special form (in eval.rs) calls into this module to:
/// 1. Compile a `.rs` file to a shared library (`.so`) via `rustc`
/// 2. Load the `.so` with `libloading`
/// 3. Register exported C ABI functions into the `FnTable`
///
/// # Plugin Contract
///
/// A plugin `.rs` file must export three C ABI functions:
///
/// ```rust,ignore
/// #[no_mangle]
/// pub extern "C" fn metta_plugin_info() -> *const std::ffi::c_char;
///
/// #[no_mangle]
/// pub extern "C" fn metta_plugin_call(
///     name: *const std::ffi::c_char,
///     args: *const std::ffi::c_char,
/// ) -> *mut std::ffi::c_char;
///
/// #[no_mangle]
/// pub extern "C" fn metta_plugin_free_string(ptr: *mut std::ffi::c_char);
/// ```
///
/// `metta_plugin_info` returns `"name1=arity;name2=arity"` (null-terminated).
/// `metta_plugin_call` receives args as a sexpr string (space-separated atoms)
/// and returns the result as a sexpr string, or null on error.
/// `metta_plugin_free_string` frees a result allocated by `call`.
use std::ffi::{CStr, CString};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{LazyLock, Mutex};

use crate::atom::Atom;
use crate::func::{FnTable, NDet};

/// Cache directory for compiled plugin `.so` files.
static CACHE_DIR: LazyLock<PathBuf> = LazyLock::new(|| {
    let dir = PathBuf::from(".mork-cache/plugins");
    let _ = std::fs::create_dir_all(&dir);
    dir
});

/// Global registry keeping loaded library handles alive (for 'static fn ptrs).
static LOADED_LIBS: LazyLock<Mutex<Vec<libloading::Library>>> =
    LazyLock::new(|| Mutex::new(Vec::new()));

// ---------------------------------------------------------------------------
// Compilation
// ---------------------------------------------------------------------------

/// Compile a `.rs` source file into a `.so` shared library.
///
/// Skips compilation if an up-to-date `.so` already exists (checks mtime).
fn compile_rs_to_so(src_path: &Path) -> Result<PathBuf, String> {
    let src_name = src_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| format!("invalid source filename: {}", src_path.display()))?;

    let so_path = CACHE_DIR.join(format!("{}.so", src_name));

    if so_path.exists() {
        let src_mtime = std::fs::metadata(src_path)
            .and_then(|m| m.modified())
            .map_err(|e| format!("reading mtime for {}: {}", src_path.display(), e))?;
        let so_mtime = std::fs::metadata(&so_path)
            .and_then(|m| m.modified())
            .map_err(|e| format!("reading mtime for {}: {}", so_path.display(), e))?;
        if so_mtime >= src_mtime {
            return Ok(so_path);
        }
    }

    let status = Command::new("rustc")
        .args([
            "--edition",
            "2021",
            "--crate-type",
            "cdylib",
            "-C",
            "opt-level=2",
            "-o",
        ])
        .arg(&so_path)
        .arg(src_path)
        .status()
        .map_err(|e| format!("failed to run rustc: {}", e))?;

    if !status.success() {
        return Err(format!(
            "rustc compilation failed for {}",
            src_path.display()
        ));
    }

    Ok(so_path)
}

// ---------------------------------------------------------------------------
// Loading + registration
// ---------------------------------------------------------------------------

/// Load a compiled `.so` plugin and register its functions into the `FnTable`.
///
/// # Safety
///
/// Loads a native shared library and resolves symbol pointers. The `.so` must
/// be from a trusted source, compatible with the current process, and compiled
/// to the same C ABI as the host.
unsafe fn load_and_register_plugin(so_path: &Path, table: &FnTable) -> Result<(), String> {
    let lib = libloading::Library::new(so_path)
        .map_err(|e| format!("loading plugin {}: {}", so_path.display(), e))?;

    // Resolve required symbols
    let info_fn: libloading::Symbol<unsafe extern "C" fn() -> *const std::ffi::c_char> = lib
        .get(b"metta_plugin_info")
        .map_err(|e| format!("plugin missing metta_plugin_info: {}", e))?;

    let call_fn: libloading::Symbol<
        unsafe extern "C" fn(
            *const std::ffi::c_char,
            *const std::ffi::c_char,
        ) -> *mut std::ffi::c_char,
    > = lib
        .get(b"metta_plugin_call")
        .map_err(|e| format!("plugin missing metta_plugin_call: {}", e))?;

    let free_fn: libloading::Symbol<unsafe extern "C" fn(*mut std::ffi::c_char)> = lib
        .get(b"metta_plugin_free_string")
        .map_err(|e| format!("plugin missing metta_plugin_free_string: {}", e))?;

    // Copy raw function pointers — they're valid as long as `lib` stays loaded.
    let call_ptr: unsafe extern "C" fn(
        *const std::ffi::c_char,
        *const std::ffi::c_char,
    ) -> *mut std::ffi::c_char = *call_fn;
    let free_ptr: unsafe extern "C" fn(*mut std::ffi::c_char) = *free_fn;

    // Read plugin info string
    let info = {
        let ptr = info_fn();
        if ptr.is_null() {
            return Err("metta_plugin_info returned null".into());
        }
        CStr::from_ptr(ptr)
            .to_str()
            .map_err(|e| format!("invalid plugin info utf8: {}", e))?
            .to_string()
    };

    // Drop Symbols before moving `lib` into the global registry
    drop(info_fn);
    drop(call_fn);
    drop(free_fn);

    // Parse function list and register each
    for entry in info.split(';') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        let Some((name, arity_str)) = entry.split_once('=') else {
            return Err(format!(
                "invalid plugin info entry: '{}' (expected 'name=arity')",
                entry
            ));
        };
        let arity: u8 = arity_str
            .parse()
            .map_err(|e| format!("invalid arity in plugin info '{}': {}", entry, e))?;
        let func_name = name.to_string();

        table.insert_native(&func_name.clone(), arity, {
            move |args: &[Atom], _table: &FnTable| {
                let args_sexpr: String = args
                    .iter()
                    .map(|a| a.to_sexpr_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                let args_cstr =
                    CString::new(args_sexpr).map_err(|e| format!("args contain null: {}", e))?;
                let name_cstr = CString::new(func_name.as_str())
                    .map_err(|e| format!("name contains null: {}", e))?;

                let result_ptr = unsafe { call_ptr(name_cstr.as_ptr(), args_cstr.as_ptr()) };

                if result_ptr.is_null() {
                    return Err(format!("plugin error calling '{}'", func_name));
                }

                let result_str = unsafe {
                    let s = CStr::from_ptr(result_ptr)
                        .to_str()
                        .map_err(|e| format!("plugin result invalid utf8: {}", e))?
                        .to_string();
                    free_ptr(result_ptr);
                    s
                };

                parse_call_result(&result_str)
            }
        });
    }

    // Keep the library alive
    LOADED_LIBS
        .write()
        .map_err(|e| format!("plugin registry lock: {}", e))?
        .push(lib);

    Ok(())
}

// ---------------------------------------------------------------------------
// Result parsing
// ---------------------------------------------------------------------------

fn parse_call_result(result: &str) -> Result<NDet, String> {
    let trimmed = result.trim();
    if let Some(msg) = trimmed.strip_prefix("ERR:") {
        return Err(format!("plugin error: {}", msg.trim()));
    }
    Ok(NDet::single(parse_plugin_atom(trimmed)?))
}

fn parse_plugin_atom(input: &str) -> Result<Atom, String> {
    let input = input.trim();
    if input.is_empty() {
        return Ok(Atom::Expr(vec![]));
    }
    if input.starts_with('(') && input.ends_with(')') {
        let inner = &input[1..input.len() - 1].trim();
        if inner.is_empty() {
            return Ok(Atom::Expr(vec![]));
        }
        let mut items = Vec::new();
        let mut depth = 0i32;
        let mut start = 0usize;
        let bytes = inner.as_bytes();
        for i in 0..bytes.len() {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                b' ' | b'\t' | b'\n' => {
                    if depth == 0 && i > start {
                        items.push(parse_plugin_atom(&inner[start..i])?);
                        start = i + 1;
                    } else if depth == 0 {
                        start = i + 1;
                    }
                }
                _ => {}
            }
        }
        if start < inner.len() {
            let token = inner[start..].trim();
            if !token.is_empty() {
                items.push(parse_plugin_atom(token)?);
            }
        }
        return Ok(Atom::Expr(items));
    }
    if let Ok(n) = input.parse::<i128>() {
        return Ok(Atom::num(n));
    }
    Ok(Atom::sym(input))
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Find, compile (if needed), load, and register a Rust plugin.
///
/// Searches `search_dirs` for `<name>.rs`, then tries bare `name` as a path.
/// Returns the library name (file stem) on success.
pub fn import_rs(name: &str, table: &FnTable, search_dirs: &[PathBuf]) -> Result<String, String> {
    let search_name = if name.ends_with(".rs") {
        name.to_string()
    } else {
        format!("{}.rs", name)
    };

    let src_path = find_rs_file(&search_name, search_dirs)?;
    let so_path = compile_rs_to_so(&src_path)?;

    // Safety: the .so was compiled from a user-provided .rs file
    unsafe { load_and_register_plugin(&so_path, table)? };

    let lib_name = src_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(name);
    Ok(lib_name.to_string())
}

fn find_rs_file(name: &str, search_dirs: &[PathBuf]) -> Result<PathBuf, String> {
    for dir in search_dirs {
        let candidate = dir.join(name);
        if candidate.exists() {
            return Ok(candidate);
        }
    }
    let bare = PathBuf::from(name);
    if bare.exists() {
        return Ok(bare);
    }
    Err(format!(
        "plugin '{}' not found in search paths: {:?}",
        name, search_dirs
    ))
}
