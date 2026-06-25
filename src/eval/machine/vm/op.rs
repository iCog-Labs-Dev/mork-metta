use crate::atom::Atom;
use crate::parser::Expr;
use crate::env::Env;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum VmExit {
    Normal,
    Cut,
    TailCall(Vec<(Atom, Env)>),
}

#[derive(Clone, Debug)]
pub struct CaseBranch {
    pub pattern: Expr,
    pub body_code: Arc<[Opcode]>,
    pub pattern_vars: Vec<String>,
    pub free_vars_map: Vec<String>,
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
    EvalCEK(Expr, Vec<String>), // Fallback to evaluate expression in CEK machine with local variable names
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
        free_vars_map: Vec<String>,
    },
    ConstEmpty,
    Cut,
    Println,
    Readln,
    Let {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        pattern_vars: Vec<String>,
        free_vars_map: Vec<String>,
    },
    If {
        then_code: Arc<[Opcode]>,
        else_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    Case {
        branches: Vec<CaseBranch>,
        local_names: Vec<String>,
    },
    Match {
        pattern: Expr,
        body_code: Arc<[Opcode]>,
        local_names: Vec<String>,
        pattern_vars: Vec<String>,
        free_vars_map: Vec<String>,
    },
    Foldall,
    Forall,
    Foldl,
    FoldlLambda {
        var_names: Vec<String>,
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    MapAtomLambda {
        var_name: String,
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    FilterAtomLambda {
        var_name: String,
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Returns only the first result from body_code.
    Once {
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Evaluates each body in sequence, discards all but the last result.
    Progn {
        bodies: Vec<Arc<[Opcode]>>,
        free_vars_map: Vec<String>,
    },
    /// Evaluates each body in sequence, discards all but the first result.
    Prog1 {
        bodies: Vec<Arc<[Opcode]>>,
        free_vars_map: Vec<String>,
    },
    /// (chain e0 $v e1 ... body): evaluates e0, binds to $v, evaluates e1, etc.
    Chain {
        /// Alternating: [expr_code, var_name, expr_code, var_name, ..., final_body_code]
        steps: Vec<(Arc<[Opcode]>, String)>,
        final_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Wraps all results from body_code into (within result1 result2 ...).
    Within {
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Pops mutex-name result from stack, runs body_code under that named mutex.
    WithMutex {
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Snapshots space state, runs body_code; restores on empty result or error.
    Transaction {
        body_code: Arc<[Opcode]>,
        free_vars_map: Vec<String>,
    },
    /// Pops space-ref from stack, loads a .metta file into it.
    ImportFile { path: String },
    /// Pops space-ref from stack (ignored), loads a .py library file.
    PythonImport { path: String },
    /// Evaluates a `(py-call expr)` — raw expression tree, not evaluated args.
    /// Bypasses dispatch.rs string matching and CEK machine entirely.
    PyCall { expr: Expr },
}
