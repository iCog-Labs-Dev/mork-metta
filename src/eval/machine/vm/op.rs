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
}
