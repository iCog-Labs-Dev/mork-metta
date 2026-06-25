use crate::atom::Atom;
use crate::parser::Expr;

#[derive(Clone, Debug)]
pub struct CaseBranch {
    pub pattern: Expr,
    pub body_code: Vec<Opcode>,
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
    UnifyPattern(Expr, u8),
    PopLocals(u8),
    AddAtom,
    RemAtom,
    DebitBudget(i64),
    Collapse,
    Superpose(u8),
    SuperposeUnpack,
    Eval,
    EvalCEK(Expr, Vec<String>), // Fallback to evaluate expression in CEK machine with local variable names
    ConstEmpty,
    Cut,
    Println,
    Readln,
    Let {
        pattern: Expr,
        body_code: Vec<Opcode>,
        pattern_vars: Vec<String>,
        free_vars_map: Vec<String>,
    },
    If {
        then_code: Vec<Opcode>,
        else_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    Case {
        branches: Vec<CaseBranch>,
        local_names: Vec<String>,
    },
    Match {
        pattern: Expr,
        body_code: Vec<Opcode>,
        local_names: Vec<String>,
        pattern_vars: Vec<String>,
        free_vars_map: Vec<String>,
    },
    Foldall,
    Forall,
    Foldl,
    FoldlLambda {
        var_names: Vec<String>,
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    MapAtomLambda {
        var_name: String,
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    FilterAtomLambda {
        var_name: String,
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Returns only the first result from body_code.
    Once {
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Evaluates each body in sequence, discards all but the last result.
    Progn {
        bodies: Vec<Vec<Opcode>>,
        free_vars_map: Vec<String>,
    },
    /// Evaluates each body in sequence, discards all but the first result.
    Prog1 {
        bodies: Vec<Vec<Opcode>>,
        free_vars_map: Vec<String>,
    },
    /// (chain e0 $v e1 ... body): evaluates e0, binds to $v, evaluates e1, etc.
    Chain {
        /// Alternating: [expr_code, var_name, expr_code, var_name, ..., final_body_code]
        steps: Vec<(Vec<Opcode>, String)>,
        final_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Wraps all results from body_code into (within result1 result2 ...).
    Within {
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Pops mutex-name result from stack, runs body_code under that named mutex.
    WithMutex {
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Snapshots space state, runs body_code; restores on empty result or error.
    Transaction {
        body_code: Vec<Opcode>,
        free_vars_map: Vec<String>,
    },
    /// Pops space-ref from stack, loads a .metta file into it.
    ImportFile { path: String },
    /// Pops space-ref from stack (ignored), loads a .py library file.
    PythonImport { path: String },
}
