pub mod cek;
pub mod constrained;
/// Decomposed evaluator module.
///
/// The `eval/` directory splits the monolithic `eval.rs` into focused
/// sub-modules, each responsible for a specific evaluation concern:
///
/// | Module | Responsibility |
/// |--------|---------------|
/// | [`core`] | Main dispatch loop, function call dispatch |
/// | [`pattern`] | Clause/pattern matching for multi-clause functions |
/// | [`data_list`] | Data-list evaluation (parallel + sequential) |
/// | [`constrained`] | Constrained evaluation with nondeterministic bindings |
/// | [`special`] | All special-form evaluators (if, let, match, foldall, …) |
/// | [`space_ops`] | Space operations (add-atom, remove-atom, match) |
/// | [`io`] | File loading, import, streaming, println, readln |
/// | [`python`] | Python bridge (optional feature) |
///
/// # Public API
///
/// Three items are re-exported for use by the crate root:
/// - [`eval_scope`](core::eval_scope) — top-level entry point
/// - [`eval`](core::eval) — evaluate an expression
/// - [`load_metta_file`](io::load_metta_file) — stream-load a `.metta` file
pub mod core;
pub mod data_list;
pub mod io;
pub mod machine;
pub mod pattern;
pub mod python;
pub mod space_ops;
pub mod special;

// Re-export public API (used by lib.rs)
pub use core::{eval_scope, eval_with_state};
pub use io::load_metta_file;
pub use machine::{MachineState, apply_substitution, calculate_cost, unify};
