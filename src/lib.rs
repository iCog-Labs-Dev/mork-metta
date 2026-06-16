/// Public API for the mork-metta evaluator.
pub mod atom;
pub mod compile;
pub mod env;
pub mod eval;
pub mod trace;
pub mod builtins;
pub mod func;
pub mod parser;
#[cfg(feature = "plugins")]
pub mod plugin;
pub mod space;

use crate::atom::Atom;
use crate::builtins::register_builtins;
use crate::compile::compile_definition;
use crate::env::Env;
use crate::func::Clause;
use crate::func::FnTable;
use crate::parser::{Expr, TopForm, expr_to_atom, parse_forms};
use crate::space::{Pattern, Space};

pub struct Runtime {
    pub funcs: FnTable,
}

impl Runtime {
    pub fn new() -> Self {
        let funcs = FnTable::new();
        register_builtins(&funcs);
        Runtime { funcs }
    }

    pub fn with_space(space: Box<dyn Space>) -> Self {
        let funcs = FnTable::with_space(space);
        register_builtins(&funcs);
        Runtime { funcs }
    }

    pub fn load_form(&mut self, form: TopForm) -> Result<Option<Atom>, String> {
        match form {
            TopForm::Definition(expr) => {
                let atom = expr_to_atom(&expr);
                self.funcs.space.write().unwrap().add_atom(&atom)?;
                if let Ok((name, clause)) = compile_definition(&expr) {
                    if let Expr::List(items) = &expr {
                        if items.len() == 3 {
                            let head_atom = crate::parser::expr_to_atom(&items[1]);
                            self.funcs.space.write().unwrap().add_atom(&head_atom)?;
                        }
                    }
                    self.funcs
                        .cache_fn(&name, clause.patterns.len() as u8, clause);
                }
                Ok(None)
            }
            TopForm::Runnable(expr) => {
                let env = Env::new();
                let (mut results, _budget) =
                    crate::eval::runtime::eval_with_state(&expr, &env, &self.funcs, None)?;
                Ok(results.next())
            }
        }
    }

    pub fn eval_str(&mut self, code: &str) -> Result<Option<Atom>, String> {
        let forms = parse_forms(code)?;
        let mut last = None;
        for form in forms {
            last = self.load_form(form)?;
        }
        Ok(last)
    }

    pub fn load_file(&mut self, path: &str) -> Result<Vec<crate::atom::Atom>, String> {
        let path = std::path::Path::new(path);
        let dir = path.parent().unwrap_or(std::path::Path::new("."));
        *self.funcs.import_dir.lock().unwrap() = dir.to_path_buf();
        let env = crate::env::Env::new();
        crate::eval::io::load_metta_file(path, &env, &self.funcs)
    }
}
