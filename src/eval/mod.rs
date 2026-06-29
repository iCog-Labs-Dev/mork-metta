//! Evaluator modules for the CEK-based runtime.
//!
//! The evaluator is organized by runtime role:
//! - `runtime` exposes public evaluation entrypoints
//! - `machine` contains execution state and stepping logic
//! - `forms` contains helpers for surface-form semantics
//! - `shared` contains reusable evaluator helpers

pub mod forms;
pub mod io;
pub mod machine;
pub mod python;
pub mod runtime;
pub mod shared;
