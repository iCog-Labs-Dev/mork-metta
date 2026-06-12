/// Public API for the mork-metta evaluator.
///
/// The `Runtime` struct is the top-level entry point: it owns the function
/// table which in turn owns the atom space and mutable state store.
///
/// # Assumptions
/// - The atom space in `funcs.space` is the single source of truth for both
///   data atoms and function definitions.
/// - The function table (`funcs`) is a materialized cache rebuilt from
///   the space via `reify_functions()`.
/// - Builtins are registered at construction time and re-registered on reify.
/// - `load_form` stores definitions in the space AND registers them as functions
///   (two-phase: data + compiled cache).

pub mod atom;
pub mod trace;
pub mod compile;
pub mod env;
pub mod eval_parts;
/// Re-export for backward compatibility with tests that import `crate::eval`.
pub mod eval {
    pub use crate::eval_parts::*;
}
pub mod func;
pub mod builtins;
pub mod parser;
pub mod space;
#[cfg(feature = "plugins")]
pub mod plugin;

use crate::atom::Atom;
use crate::compile::compile_definition;
use crate::env::Env;
use crate::eval_parts::{eval, eval_scope};
use crate::func::FnTable;
use crate::func::Clause;
use crate::builtins::register_builtins;
use crate::parser::{expr_to_atom, parse_forms, Expr, TopForm};
use crate::space::{Pattern, Space};

/// The MeTTa runtime: owns the function table (which owns the atom space).
pub struct Runtime {
    /// Derived function dispatch table (also owns the atom space + state store).
    pub funcs: FnTable,
}

impl Runtime {
    /// Create a new runtime with a `LocalSpace` backend.
    pub fn new() -> Self {
        let funcs = FnTable::new();
        register_builtins(&funcs);
        Runtime { funcs }
    }

    /// Create a new runtime with a specific space backend.
    pub fn with_space(space: Box<dyn Space>) -> Self {
        let funcs = FnTable::with_space(space);
        register_builtins(&funcs);
        Runtime { funcs }
    }

    /// Rebuild the function table by scanning the space for `(= ...)` atoms.
    pub fn reify_functions(&mut self) {
        let pat = Pattern::Expr(vec![
            Pattern::Exact(Atom::sym("=")),
            Pattern::Any,
            Pattern::Any,
        ]);
        // Snapshot matches while holding space lock
        let matches: Vec<_> = {
            let space = self.funcs.space.lock().unwrap();
            space.match_atoms(&pat)
        };
        // Snapshot state
        let state: std::collections::HashMap<String, Atom> = {
            let s = self.funcs.state.lock().unwrap();
            s.clone()
        };
        // Move space out of current table
        let old_space = std::mem::replace(
            &mut *self.funcs.space.lock().unwrap(),
            crate::space::LocalSpace::new_box(),
        );
        // Fresh table
        let new_table = FnTable::new();
        register_builtins(&new_table);
        // Move space and state into new table
        let _ = std::mem::replace(&mut *new_table.space.lock().unwrap(), old_space);
        let _ = std::mem::replace(&mut *new_table.state.lock().unwrap(), state);
        // Re-register user-defined functions
        for result in matches {
            if let Ok(expr) = parser::atom_to_expr(&result.atom) {
                if let Ok((name, clause)) = compile_definition(&expr) {
                    new_table.add_clause(name, clause.patterns, clause.body);
                }
            }
        }
        self.funcs = new_table;
    }

    /// Process a single top-level form.
    ///
    /// - `Definition` → store the atom in the space, compile the function,
    ///   and register it. Returns `Ok(None)`.
    /// - `Runnable` → evaluate the expression. Returns `Ok(Some(result))` where
    ///   result is the first atom from the evaluation stream, or `None` if the
    ///   stream is empty (no results).
    ///
    /// # Assumptions
    /// - Definitions do not produce a return value (return `None`).
    /// - Runnable forms collect the FIRST result only (caller uses `collapse`
    ///   explicitly for multiple results).
    pub fn load_form(&mut self, form: TopForm) -> Result<Option<Atom>, String> {
        match form {
            TopForm::Definition(expr) => {
                // Store the atom in the space unconditionally — plain data atoms
                // like `(kb 1)` are valid top-level forms that go into &self.
                let atom = expr_to_atom(&expr);
                self.funcs.space.lock().unwrap().add_atom(&atom)?;
                // Only compile as a function if it's a (= head body) form.
                if let Ok((name, clause)) = compile_definition(&expr) {
                    // Also store the BARE HEAD atom so `match` can find premise atoms
                    if let Expr::List(items) = &expr {
                        if items.len() == 3 {
                            let head_atom = crate::parser::expr_to_atom(&items[1]);
                            self.funcs.space.lock().unwrap().add_atom(&head_atom)?;
                        }
                    }
                    self.funcs.add_clause(name, clause.patterns, clause.body);
                }
                Ok(None)
            }
            TopForm::Runnable(expr) => {
                let env = Env::new();
                let mut results = eval_scope(&expr, &env, &self.funcs)?;
                Ok(results.next())
            }
        }
    }

    /// Parse and process a MeTTa source string.
    pub fn eval_str(&mut self, code: &str) -> Result<Option<Atom>, String> {
        let forms = parse_forms(code)?;
        let mut last = None;
        for form in forms {
            last = self.load_form(form)?;
        }
        Ok(last)
    }

    /// Load and process a `.metta` file with streaming form-by-form parsing.
    ///
    /// Unlike `eval_str`, this never loads the whole file into memory — safe for
    /// files with millions of atom assertions. Sets `import_dir` to the file's
    /// parent directory so that `import!` inside the file resolves paths relative
    /// to the file, not the caller's CWD.
    pub fn load_file(&mut self, path: &str) -> Result<Vec<crate::atom::Atom>, String> {
        let path = std::path::Path::new(path);
        let dir = path.parent().unwrap_or(std::path::Path::new("."));
        *self.funcs.import_dir.lock().unwrap() = dir.to_path_buf();
        let env = crate::env::Env::new();
        crate::eval_parts::load_metta_file(path, &env, &self.funcs)
    }
}
