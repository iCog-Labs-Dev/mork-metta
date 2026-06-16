//! Execution machine for the evaluator.
//!
//! This module tree contains the runtime state, continuation frames, work
//! scheduling, syntax dispatch, frame application, stepping, and cost
//! accounting used during evaluation.

pub mod apply;
pub mod budget;
pub mod dispatch;
pub mod frame;
pub mod state;
pub mod step;
pub mod task;
pub mod transition;
