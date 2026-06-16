//! Registration entrypoints for native builtins.

pub mod arithmetic;
pub mod boolean;
pub mod collections;
pub mod io;
pub mod state;
pub mod types;

use crate::func::FnTable;

/// Register all built-in functions.
pub fn register_builtins(funcs: &FnTable) {
    arithmetic::register_arithmetic_builtins(funcs);
    boolean::register_boolean_builtins(funcs);
    collections::register_collection_builtins(funcs);
    io::register_io_builtins(funcs);
    state::register_state_builtins(funcs);
    types::register_type_builtins(funcs);
}
