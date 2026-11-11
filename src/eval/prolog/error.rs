use std::ffi::NulError;
use thiserror::Error;
use crate::atom::Atom;

#[derive(Debug, Clone, Error)]
pub enum PrologError {
    #[error("SWI-Prolog library not found: {0}")]
    LibraryNotFound(String),
    #[error("PL_initialise failed: {0}")]
    InitFailed(String),
    #[error("Prolog exception: {0}")]
    Exception(String),
    #[error("term conversion failed: {0}")]
    Conversion(String),
    #[error("internal error: {0}")]
    Internal(String),
}

impl From<NulError> for PrologError {
    fn from(e: NulError) -> Self { PrologError::Conversion(e.to_string()) }
}

impl PrologError {
    pub fn to_error_atom(&self, context: &Atom) -> Atom {
        Atom::expr(vec![
            Atom::sym("Error"),
            context.clone(),
            Atom::str_val(&self.to_string()),
        ])
    }
}
