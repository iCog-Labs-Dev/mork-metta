//! Atomspace modules.
//!
//! `core` owns the Space trait, MorkSpace backend, Pattern, and MatchResult.
//! `store`, `mutate`, and `query` wrap FnTable-level operations over spaces.

pub mod core;
pub mod mutate;
pub mod query;
pub mod store;

pub use core::{MatchResult, MorkSpace, Pattern, Space, parse_one_atom};
