use crate::atom::Atom;
use crate::parser::Expr;
use super::op::{Opcode, CaseBranch};

pub struct VMCompiler {
    pub locals: Vec<String>,
    pub free_vars: Vec<String>,
    pub fn_name: Option<String>,
    pub arity: usize,
}

impl VMCompiler {
    pub fn new(patterns: &[Expr], fn_name: Option<String>) -> Self {
        let mut locals = Vec::new();
        for pat in patterns {
            collect_pattern_vars(pat, &mut locals);
        }
        let arity = locals.len();
        VMCompiler {
            locals,
            free_vars: Vec::new(),
            fn_name,
            arity,
        }
    }

    pub fn compile(&mut self, expr: &Expr, code: &mut Vec<Opcode>, is_tail: bool) -> Result<(), String> {
        match expr {
            Expr::Symbol(s) => {
                if s.starts_with('$') {
                    if let Some(pos) = self.locals.iter().rposition(|x| x == s) {
                        code.push(Opcode::Load(pos as u8));
                    } else {
                        let pos = if let Some(p) = self.free_vars.iter().position(|x| x == s) {
                            p
                        } else {
                            self.free_vars.push(s.clone());
                            self.free_vars.len() - 1
                        };
                        code.push(Opcode::LoadFree(pos as u8));
                    }
                } else {
                    code.push(Opcode::Const(Atom::sym(s)));
                }
            }
            Expr::Str(s) => {
                code.push(Opcode::Const(Atom::str_val(s)));
            }
            Expr::Number(n) => {
                code.push(Opcode::Const(Atom::Num(n.clone())));
            }
            Expr::List(items) => {
                if items.is_empty() {
                    code.push(Opcode::Const(Atom::Expr(crate::atom::expr_data([]))));
                    return Ok(());
                }

                if let Expr::Symbol(head) = &items[0] {
                    match head.as_str() {
                        "quote" if items.len() == 2 => {
                            let atom = crate::parser::expr_to_atom(&items[1]);
                            code.push(Opcode::Const(atom));
                            return Ok(());
                        }
                        "empty" if items.len() == 1 => {
                            code.push(Opcode::ConstEmpty);
                            return Ok(());
                        }
                        "cut" if items.len() == 1 => {
                            code.push(Opcode::Cut);
                            return Ok(());
                        }
                        "println!" if items.len() == 2 => {
                            self.compile(&items[1], code, false)?;
                            code.push(Opcode::Println);
                            return Ok(());
                        }
                        "readln!" if items.len() == 1 => {
                            code.push(Opcode::Readln);
                            return Ok(());
                        }
                        "eval" if items.len() == 2 => {
                            self.compile(&items[1], code, false)?;
                            code.push(Opcode::Eval);
                            return Ok(());
                        }
                        "call" | "reduce" if items.len() == 2 => {
                            // ponytail: call and reduce are compiled by directly compiling their argument as they have the same evaluation result.
                            self.compile(&items[1], code, is_tail)?;
                            return Ok(());
                        }
                        "if" if items.len() == 3 || items.len() == 4 => {
                            self.compile(&items[1], code, false)?; // Compile condition
                            
                            let mut then_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut then_code = Vec::new();
                            then_comp.compile(&items[2], &mut then_code, is_tail)?;
                            
                            let mut else_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut else_code = Vec::new();
                            if items.len() == 4 {
                                else_comp.compile(&items[3], &mut else_code, is_tail)?;
                            }
                            
                            // Combine free vars
                            let mut union_free_vars = self.free_vars.clone();
                            for v in &then_comp.free_vars {
                                if !union_free_vars.contains(v) { union_free_vars.push(v.clone()); }
                            }
                            for v in &else_comp.free_vars {
                                if !union_free_vars.contains(v) { union_free_vars.push(v.clone()); }
                            }
                            self.free_vars = union_free_vars.clone();
                            
                            code.push(Opcode::If {
                                then_code,
                                else_code,
                                free_vars_map: union_free_vars,
                            });
                            return Ok(());
                        }
                        "case" if items.len() == 3 => {
                            let Expr::List(clauses) = &items[2] else {
                                return Err("case clauses must be a list".into());
                            };
                            self.compile(&items[1], code, false)?;
                            
                            let mut compiled_branches = Vec::new();
                            let mut union_free_vars = self.free_vars.clone();
                            for clause in clauses.iter() {
                                let (pattern, body) = match clause {
                                    Expr::List(clause_items) if clause_items.len() == 2 => (&clause_items[0], &clause_items[1]),
                                    _ => return Err("case clause must be a list of 2 items".into()),
                                };
                                
                                let mut body_comp = VMCompiler {
                                    locals: self.locals.clone(),
                                    free_vars: union_free_vars.clone(),
                                    fn_name: None,
                                    arity: self.arity,
                                };
                                
                                let mut pattern_vars = Vec::new();
                                collect_pattern_vars(pattern, &mut pattern_vars);
                                body_comp.locals.extend(pattern_vars.clone());
                                
                                let mut branch_code = Vec::new();
                                body_comp.compile(body, &mut branch_code, is_tail)?;
                                
                                for v in &body_comp.free_vars {
                                    if !union_free_vars.contains(v) {
                                        union_free_vars.push(v.clone());
                                    }
                                }
                                
                                compiled_branches.push(CaseBranch {
                                    pattern: pattern.clone(),
                                    body_code: branch_code,
                                    pattern_vars,
                                    free_vars_map: body_comp.free_vars,
                                });
                            }
                            self.free_vars = union_free_vars;
                            
                            code.push(Opcode::Case {
                                branches: compiled_branches,
                                local_names: self.locals.clone(),
                            });
                            return Ok(());
                        }
                        "match" if items.len() == 4 => {
                            self.compile(&items[1], code, false)?;
                            
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: None,
                                arity: self.arity,
                            };
                            let mut pattern_vars = Vec::new();
                            collect_pattern_vars(&items[2], &mut pattern_vars);
                            body_comp.locals.extend(pattern_vars.clone());
                            
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[3], &mut body_code, true)?;
                            
                            code.push(Opcode::Match {
                                pattern: items[2].clone(),
                                body_code,
                                local_names: self.locals.clone(),
                                pattern_vars,
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "collapse" if items.len() == 2 => {
                            self.compile(&items[1], code, false)?;
                            code.push(Opcode::Collapse);
                            return Ok(());
                        }
                        "superpose" if items.len() == 2 => {
                            if let Expr::List(elems) = &items[1] {
                                for elem in elems.iter() {
                                    self.compile(elem, code, false)?;
                                }
                                code.push(Opcode::Superpose(elems.len() as u8));
                            } else {
                                self.compile(&items[1], code, false)?;
                                code.push(Opcode::SuperposeUnpack);
                            }
                            return Ok(());
                        }
                        "let" if items.len() == 4 => {
                            // ponytail: Let matches value and binds pattern variables to locals before executing body
                            self.compile(&items[2], code, false)?;
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut pattern_vars = Vec::new();
                            collect_pattern_vars(&items[1], &mut pattern_vars);
                            body_comp.locals.extend(pattern_vars.clone());

                            let mut body_code = Vec::new();
                            body_comp.compile(&items[3], &mut body_code, is_tail)?;

                            for v in &body_comp.free_vars {
                                if !self.free_vars.contains(v) {
                                    self.free_vars.push(v.clone());
                                }
                            }
                            code.push(Opcode::Let {
                                pattern: items[1].clone(),
                                body_code,
                                pattern_vars,
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "let*" if items.len() == 3 => {
                            // ponytail: let* desugared into nested let instructions recursively
                            let bindings = match &items[1] {
                                Expr::List(b) => b,
                                _ => return Err("let*: bindings must be a list".into()),
                            };
                            self.compile_let_star(bindings, 0, &items[2], code, is_tail)?;
                            return Ok(());
                        }
                        "foldall" if items.len() == 4 => {
                            // ponytail: foldall aggregates values from generator over initial value
                            self.compile(&items[2], code, false)?;
                            self.compile(&items[3], code, false)?;
                            self.compile(&items[1], code, false)?;
                            code.push(Opcode::Foldall);
                            return Ok(());
                        }
                        "forall" if items.len() == 3 => {
                            // ponytail: forall checks if all values of generator satisfy condition
                            self.compile(&items[1], code, false)?;
                            self.compile(&items[2], code, false)?;
                            code.push(Opcode::Forall);
                            return Ok(());
                        }
                        "foldl-atom" if items.len() == 4 => {
                            // ponytail: foldl-atom Form 1 (with accumulator function)
                            self.compile(&items[1], code, false)?;
                            self.compile(&items[2], code, false)?;
                            self.compile(&items[3], code, false)?;
                            code.push(Opcode::Foldl);
                            return Ok(());
                        }
                        "foldl-atom" if items.len() >= 5 => {
                            // ponytail: foldl-atom Form 2 (with variable names and body expression)
                            self.compile(&items[1], code, false)?;
                            self.compile(&items[2], code, false)?;
                            let mut var_names = Vec::new();
                            for item in &items[3..items.len() - 1] {
                                match item {
                                    Expr::Symbol(s) => var_names.push(s.clone()),
                                    _ => return Err("foldl-atom: expected variable symbol".into()),
                                }
                            }
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            body_comp.locals.extend(var_names.clone());
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[items.len() - 1], &mut body_code, false)?;

                            for v in &body_comp.free_vars {
                                if !self.free_vars.contains(v) {
                                    self.free_vars.push(v.clone());
                                }
                            }
                            code.push(Opcode::FoldlLambda {
                                var_names,
                                body_code,
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        // For any other special keyword/construct (e.g. once, etc.), fallback to EvalCEK
                        "|->" | "map-atom" | "filter-atom" | "within" | "once" | "progn" | "prog1" | "chain" | "add-atom" | "remove-atom" => {
                            code.push(Opcode::EvalCEK(expr.clone(), self.locals.clone()));
                            return Ok(());
                        }
                        _ => {}
                    }
                }

                // General application
                let arity = items.len() - 1;
                if is_tail {
                    if let Some(ref fname) = self.fn_name {
                        if let Expr::Symbol(hname) = &items[0] {
                            if hname == fname && arity == self.arity {
                                for i in 1..items.len() {
                                    self.compile(&items[i], code, false)?;
                                }
                                for i in (1..items.len()).rev() {
                                    code.push(Opcode::Store((i - 1) as u8));
                                }
                                code.push(Opcode::Jump(0));
                                return Ok(());
                            }
                        }
                    }
                }
                for i in 1..items.len() {
                    self.compile(&items[i], code, false)?;
                }
                self.compile(&items[0], code, false)?;
                code.push(Opcode::Call(arity as u8));
            }
        }
        Ok(())
    }

    fn compile_let_star(
        &mut self,
        bindings: &[Expr],
        bind_idx: usize,
        body: &Expr,
        code: &mut Vec<Opcode>,
        is_tail: bool,
    ) -> Result<(), String> {
        if bind_idx >= bindings.len() {
            self.compile(body, code, is_tail)?;
            return Ok(());
        }
        let (pattern, value_expr) = match &bindings[bind_idx] {
            Expr::List(pair) if pair.len() == 2 => (&pair[0], &pair[1]),
            _ => return Err("let*: each binding must be a list of 2 items".into()),
        };
        self.compile(value_expr, code, false)?;
        let mut body_comp = VMCompiler {
            locals: self.locals.clone(),
            free_vars: self.free_vars.clone(),
            fn_name: self.fn_name.clone(),
            arity: self.arity,
        };
        let mut pattern_vars = Vec::new();
        collect_pattern_vars(pattern, &mut pattern_vars);
        body_comp.locals.extend(pattern_vars.clone());

        let mut body_code = Vec::new();
        body_comp.compile_let_star(bindings, bind_idx + 1, body, &mut body_code, is_tail)?;

        for v in &body_comp.free_vars {
            if !self.free_vars.contains(v) {
                self.free_vars.push(v.clone());
            }
        }
        code.push(Opcode::Let {
            pattern: pattern.clone(),
            body_code,
            pattern_vars,
            free_vars_map: body_comp.free_vars,
        });
        Ok(())
    }
}

fn collect_pattern_vars(expr: &Expr, set: &mut Vec<String>) {
    match expr {
        Expr::Symbol(s) if s.starts_with('$') => {
            if !set.contains(s) {
                set.push(s.clone());
            }
        }
        Expr::List(items) => {
            for item in items.iter() {
                collect_pattern_vars(item, set);
            }
        }
        _ => {}
    }
}
