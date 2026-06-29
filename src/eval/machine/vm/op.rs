use crate::atom::Atom;
use crate::env::Env;
use crate::parser::Expr;
use std::sync::Arc;

pub enum VmExit {
    Normal,
    Cut,
    TailCall(Vec<(Atom, Env)>),
    /// Trampoline: yield execution to a sub-VM. Both states are boxed to
    /// break the layout cycle (VMState contains VmExit via last_sub_result).
    YieldCall {
        parent_state: Box<super::state::VMState>,
        parent_env: Env,
        sub_state: Box<super::state::VMState>,
        sub_env: Env,
    },
}

// Manual Debug so we don't require Debug on VMState (which holds Box<dyn Any>).
impl std::fmt::Debug for VmExit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VmExit::Normal => write!(f, "VmExit::Normal"),
            VmExit::Cut => write!(f, "VmExit::Cut"),
            VmExit::TailCall(locals) => write!(f, "VmExit::TailCall({} locals)", locals.len()),
            VmExit::YieldCall { .. } => write!(f, "VmExit::YieldCall {{ .. }}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CaseBranch {
    pub pattern: Expr,
    pub body_code: Arc<[Opcode]>,
    pub pattern_vars: Vec<String>,
    pub free_vars_map: Arc<[String]>,
}

#[derive(Clone, Debug)]
pub enum Opcode {
    Const(Atom),
    Load(u8),
    Store(u8),
    LoadFree(u8),
    Pop,
    Jump(usize),
    JumpIfEmpty(usize),
    JumpIfFalsy(usize),
    Call(u8),
    TailCallSelf,
    UnifyPattern(Expr, u8),
    PopLocals(u8),
    AddAtom {
        expr: Expr,
        local_names: Vec<String>,
    },
    RemAtom {
        expr: Expr,
        local_names: Vec<String>,
    },
    DebitBudget(i64),
    Collapse,
    Superpose(u8),
    SuperposeUnpack,
    Eval,
    Lambda {
        params: Vec<Expr>,
        body: Expr,
        local_names: Vec<String>,
    },
    Unify {
        pattern_a: Expr,
        pattern_b: Expr,
        then_code: Arc<[Opcode]>,
        else_code: Arc<[Opcode]>,
        pattern_vars: Vec<String>,
        local_names: Vec<String>,
        free_vars_map: Arc<[String]>,
    },
    ConstEmpty,
    Cut,
    Println,
    Readln,
    Let {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        pattern_vars: Vec<String>,
        free_vars_map: Arc<[String]>,
    },
    If {
        then_code: Arc<[Opcode]>,
        else_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    Case {
        branches: Vec<CaseBranch>,
    },
    Match {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        local_names: Vec<String>,
        pattern_vars: Vec<String>,
        free_vars_map: Arc<[String]>,
    },
    Foldall,
    Forall,
    Foldl,
    FoldlLambda {
        var_names: Vec<String>,
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    MapAtomLambda {
        var_name: String,
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    FilterAtomLambda {
        var_name: String,
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Returns only the first result from body_code.
    Once {
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Evaluates each body in sequence, discards all but the last result.
    Progn {
        bodies: Vec<Arc<[Opcode]>>,
        free_vars_map: Arc<[String]>,
    },
    /// Evaluates each body in sequence, discards all but the first result.
    Prog1 {
        bodies: Vec<Arc<[Opcode]>>,
        free_vars_map: Arc<[String]>,
    },
    /// (chain e0 $v e1 ... body): evaluates e0, binds to $v, evaluates e1, etc.
    Chain {
        /// Alternating: [expr_code, var_name, expr_code, var_name, ..., final_body_code]
        steps: Vec<(Arc<[Opcode]>, String)>,
        final_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Wraps all results from body_code into (within result1 result2 ...).
    Within {
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Pops mutex-name result from stack, runs body_code under that named mutex.
    WithMutex {
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Snapshots space state, runs body_code; restores on empty result or error.
    Transaction {
        body_code: Arc<[Opcode]>,
        free_vars_map: Arc<[String]>,
    },
    /// Pops space-ref from stack, loads a .metta file into it.
    ImportFile {
        path: String,
    },
    /// Pops space-ref from stack (ignored), loads a .py library file.
    PythonImport {
        path: String,
    },
    /// Evaluates a `(py-call expr)` — raw expression tree, not evaluated args.
    /// Bypasses dispatch.rs string matching and CEK machine entirely.
    PyCall {
        expr: Expr,
    },
    PyEval {
        expr: Expr,
    },
    ImportDynamic,
    /// Test special form: evaluates expression, collects ALL non-deterministic results,
    /// compares with expected value (structural equality), prints "is X, should Y. ✅/❌",
    /// and always returns True. Matches PeTTa's `test` keyword behavior.
    Test,
    MapAtomPatternLambda {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        pattern_vars: Vec<String>,
        free_vars_map: Arc<[String]>,
    },
    FilterAtomPatternLambda {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        pattern_vars: Vec<String>,
        free_vars_map: Arc<[String]>,
    },
    ConstQuote {
        template: Atom,
        vars: Vec<QuoteVarMatch>,
    },
}

#[derive(Clone, Debug)]
pub enum QuoteVarSource {
    Local(u8),
    Free(u8),
}

#[derive(Clone, Debug)]
pub struct QuoteVarMatch {
    pub path: Vec<usize>,
    pub source: QuoteVarSource,
}
