//! Continuation frames used during evaluation.
//!
//! A frame represents a suspended evaluation context. Frames capture the
//! information needed to continue evaluation after a child expression produces
//! a result.

use super::budget::ResultSet;
use super::task::Head;
use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use std::sync::Arc;

/// A suspended continuation frame.
pub(crate) enum Frame {
    /// Resume a function application after its arguments have been evaluated.
    Call {
        /// The selected callable head.
        head: Head,
        /// The number of argument positions in the call.
        arity: usize,
        /// The environment active at the call site.
        env: Env,
        /// Prebound argument slots used when some arguments were materialized
        /// before the remaining argument tasks were scheduled.
        prebound_args: Option<Vec<Option<ResultSet>>>,
    },
    /// Reconstruct a data list after all element result sets are available.
    DataList {
        /// The number of element result sets consumed by this frame.
        n: usize,
    },
    /// Reconstruct a data list whose head value is already known.
    DataListWithHead {
        /// The already-evaluated head atom.
        head: Atom,
        /// The number of tail result sets consumed by this frame.
        n_tail: usize,
    },
    /// Concatenate multiple child result sets.
    Gather {
        /// The number of child result sets consumed by this frame.
        n: usize,
    },
    /// Collect branch results produced by conditional evaluation.
    IfGather {
        /// Whether the original conditional carried explicit branch bindings.
        had_bindings: bool,
        /// The number of branch result sets consumed by this frame.
        n: usize,
    },
    /// Select `case` branches from evaluated scrutinee results.
    CaseSelect {
        /// Ordered clause list.
        clauses: Arc<Vec<Expr>>,
        /// Environment active outside branch-local evaluation.
        env: Env,
    },
    /// Wrap a child result as a `within` expression result.
    WithinWrap,
    /// Collapse a child result stream into a single list atom.
    CollapseGather,
    /// Merge a stored environment into the results of a child evaluation.
    MergeEnv {
        /// Environment to prepend to each result.
        env: Env,
    },
    /// Keep only the first result produced by a child expression.
    OnceCut,
    /// Continue a `chain` form after one pair has been evaluated and bound.
    ChainBind {
        /// The original chain arguments.
        args: Arc<Vec<Expr>>,
        /// The index of the current pair within the chain.
        pair_index: usize,
        /// The environment active after previous bindings.
        env: Env,
    },
    /// Continue a `let*` form after one binding value has been evaluated.
    LetStarBind {
        /// Sequential binding list.
        bindings: Arc<Vec<Expr>>,
        /// Current binding index.
        bind_index: usize,
        /// Body evaluated after all bindings succeed.
        body: Arc<Expr>,
        /// Environment active before matching the current binding result.
        env: Env,
    },
    /// Match atoms in a resolved space and continue with the body.
    SpaceMatch {
        /// Surface pattern matched in the target space.
        pattern: Expr,
        /// Body evaluated for each successful space match.
        body: Arc<Expr>,
        /// Environment active outside the space-match bindings.
        env: Env,
    },
    /// Resolve a space reference and add one atom to that space.
    SpaceAdd {
        /// Surface atom inserted after substitution.
        atom: Expr,
        /// Environment active when the atom is materialized.
        env: Env,
    },
    /// Resolve a space reference and remove one atom from that space.
    SpaceRemove {
        /// Surface atom removed after substitution.
        atom: Expr,
        /// Environment active when the atom is materialized.
        env: Env,
    },
    /// Resolve a mutex name and evaluate the body while the mutex is held.
    MutexEnter {
        /// Body evaluated under the named mutex.
        body: Arc<Expr>,
        /// Environment active around the mutex body.
        env: Env,
    },
    /// Unpack the result of `superpose` when it is an expression atom.
    SuperposeUnpack,
    /// Match a `let` pattern against a computed value and continue with the
    /// body for each successful match.
    LetMatch {
        pattern: Expr,
        body: Arc<Expr>,
        env: Env,
    },
    /// Collect 3 evaluated args (list, acc, func) and start a fold loop.
    FoldlInit,
    /// Print the evaluated argument, return it.
    Println,
    /// Apply a head value (closure or symbol) to previously evaluated arguments.
    ///
    /// The head is popped after the arguments, so arguments are evaluated first
    /// (in the usual reverse task order). The frame then matches the head value:
    /// - Closure: apply closure with the evaluated arguments
    /// - Symbol: dispatch as a function call
    /// - Other: construct a data list
    ApplyHead {
        /// The number of argument result sets consumed by this frame.
        arity: usize,
        /// Environment for evaluating the head expression.
        env: Env,
    },
    /// Load a MeTTa file after the space-ref arg is evaluated.
    ImportFile {
        path: String,
        env: Env,
    },
    /// One step of foldl-atom: apply result as new acc, continue fold.
    FoldlAtom {
        /// All items in the list being folded.
        items: Arc<Vec<Atom>>,
        /// Next index to fold over.
        index: usize,
        /// Current accumulator (before this step's result).
        acc: Atom,
        /// Function atom (symbol) applied each step.
        func: Atom,
    },
}
