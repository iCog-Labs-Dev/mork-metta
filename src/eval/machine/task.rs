//! Work items scheduled by the evaluator.
//!
//! Tasks represent units of machine work such as evaluating an expression,
//! resuming a continuation, or processing grouped subcomputations.

use super::frame::Frame;
use super::state::Transition;
use crate::atom::Atom;
use crate::env::Env;
use crate::func::{FnTable, NDet};
use crate::parser::Expr;
use std::sync::Arc;

/// The callable head selected for a function application.
pub(crate) enum Head {
    /// A native Rust function registered in the evaluator.
    Native(Arc<dyn Fn(&[Atom], &FnTable) -> Result<NDet, String> + Send + Sync + 'static>),
    /// A user-defined function represented by its clause bodies and lazy slots.
    User {
        /// The surface name of the function.
        name: String,
        /// The function clauses used for query-style application.
        clauses: Vec<(Vec<Expr>, Expr)>,
        /// A per-argument mask indicating which positions are passed lazily.
        lazy_mask: Vec<bool>,
    },
}

/// A unit of scheduled machine work.
pub(crate) enum Task {
    /// Evaluate an expression in an environment.
    Eval {
        /// The expression to evaluate.
        expr: Arc<Expr>,
        /// The environment in which the expression is evaluated.
        env: Env,
    },
    /// Apply a suspended continuation frame.
    Apply(Frame),
    Transition(Transition),
}
