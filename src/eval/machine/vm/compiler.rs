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
                        // For any other special keyword/construct (e.g. let, let*, once, etc.), fallback to EvalCEK
                        "let" | "let*" | "once" | "progn" | "prog1" | "chain" | "add-atom" | "remove-atom" => {
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
