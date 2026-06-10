/// Public API for the mork-metta evaluator.
///
/// The `Runtime` struct is the top-level entry point: it owns the atom space
/// and the derived function table. Users create a Runtime, load MeTTa source
/// with `eval_str` or `load_file`, and inspect the results.
///
/// # Assumptions
/// - The atom space (`self_space`) is the single source of truth for both
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
pub mod eval;
pub mod func;
pub mod builtins;
pub mod parser;
pub mod space;

use crate::atom::Atom;
use crate::compile::compile_definition;
use crate::env::Env;
use crate::eval::eval;
use crate::func::FnTable;
use crate::func::Clause;
use crate::builtins::register_builtins;
use crate::parser::{expr_to_atom, parse_forms, TopForm};
use crate::space::{Pattern, Space};

/// The MeTTa runtime: owns the atom space and the derived function table.
///
/// The `&self` space is the single source of truth — both data atoms and
/// function definitions live here. The function table is a materialized
/// cache rebuilt by `reify_functions()`.
pub struct Runtime {
    /// The `&self` atom space — unified storage for data and code.
    pub self_space: Box<dyn Space>,
    /// Derived function dispatch table (rebuilt from `self_space`).
    pub funcs: FnTable,
}

impl Runtime {
    /// Create a new runtime with a `LocalSpace` backend.
    pub fn new() -> Self {
        Runtime::with_space(Box::new(space::LocalSpace::new()))
    }

    /// Create a new runtime with a specific space backend.
    pub fn with_space(space: Box<dyn Space>) -> Self {
        let mut funcs = FnTable::new();
        register_builtins(&mut funcs);
        Runtime {
            self_space: space,
            funcs,
        }
    }

    /// Rebuild the function table by scanning the self space for `(= ...)` atoms.
    ///
    /// This is called automatically after `load_form` for definitions, and can
    /// be called manually after bulk-loading atoms into the space.
    ///
    /// # Assumptions
    /// - Builtins are re-registered first (they take precedence over user defs).
    /// - Multi-clause functions are accumulated: each `(= ...)` atom in the space
    ///   adds one clause, so multiple definitions of the same name produce
    ///   multi-clause dispatch.
    pub fn reify_functions(&mut self) {
        self.funcs = FnTable::new();
        register_builtins(&mut self.funcs);
        // Match all (= head body) forms in the self space
        let pat = Pattern::Expr(vec![
            Pattern::Exact(Atom::sym("=")),
            Pattern::Any, // head expression
            Pattern::Any, // body expression
        ]);
        let mut pending: Vec<(String, Clause)> = Vec::new();
        for result in self.self_space.match_atoms(&pat) {
            if let Ok(expr) = parser::atom_to_expr(&result.atom) {
                if let Ok((name, clause)) = compile_definition(&expr) {
                    pending.push((name, clause));
                }
            }
        }
        for (name, clause) in pending {
            self.funcs.add_clause(name, clause.patterns, clause.body);
        }
    }
    /// Process a single top-level form.
    ///
    /// - `Definition` → store the atom in the self space, compile the function,
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
                let (name, clause) = compile_definition(&expr)?;
                // Store the raw definition atom in the self space
                let atom = expr_to_atom(&expr);
                self.self_space.add_atom(&atom)?;
                // Register clause in the function table
                self.funcs.add_clause(name, clause.patterns, clause.body);
                Ok(None)
            }
            TopForm::Runnable(expr) => {
                let env = Env::new();
                let mut results = eval(&expr, &env, &self.funcs)?;
                Ok(results.next())
            }
        }
    }

    /// Parse and process a MeTTa source string.
    ///
    /// Returns the result of the **last** runnable form's first result, if any.
    ///
    /// # Assumptions
    /// - Only the first result of each runnable form is returned.
    /// - Definitions in the string are loaded into the space and func table.
    pub fn eval_str(&mut self, code: &str) -> Result<Option<Atom>, String> {
        let forms = parse_forms(code)?;
        let mut last = None;
        for form in forms {
            last = self.load_form(form)?;
        }
        Ok(last)
    }

    /// Load and process a `.metta` file.
    ///
    /// Reads the file, parses it, and processes all forms.
    /// Returns the result of the last runnable form, if any.
    pub fn load_file(&mut self, path: &str) -> Result<Option<Atom>, String> {
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("cannot read file: {}", e))?;
        self.eval_str(&content)
    }
}
