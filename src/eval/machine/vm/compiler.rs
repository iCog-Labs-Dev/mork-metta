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
                        "empty" => {
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
                                then_code: std::sync::Arc::from(then_code),
                                else_code: std::sync::Arc::from(else_code),
                                free_vars_map: union_free_vars,
                            });
                            return Ok(());
                        }
                        // ponytail: desugar and/or to if only when both arguments are expressions (lists) to allow logic variable unification on simple symbols
                        "and" if items.len() == 3 && matches!(&items[1], Expr::List(_)) && matches!(&items[2], Expr::List(_)) => {
                            let desugared = Expr::List(std::sync::Arc::from([
                                Expr::Symbol("if".to_string()),
                                items[1].clone(),
                                items[2].clone(),
                                Expr::Symbol("False".to_string()),
                            ]));
                            self.compile(&desugared, code, is_tail)?;
                            return Ok(());
                        }
                        "or" if items.len() == 3 && matches!(&items[1], Expr::List(_)) && matches!(&items[2], Expr::List(_)) => {
                            let desugared = Expr::List(std::sync::Arc::from([
                                Expr::Symbol("if".to_string()),
                                items[1].clone(),
                                Expr::Symbol("True".to_string()),
                                items[2].clone(),
                            ]));
                            self.compile(&desugared, code, is_tail)?;
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
                                    fn_name: self.fn_name.clone(),
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
                                    body_code: std::sync::Arc::from(branch_code),
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
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut pattern_vars = Vec::new();
                            collect_pattern_vars(&items[2], &mut pattern_vars);
                            body_comp.locals.extend(pattern_vars.clone());
                            
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[3], &mut body_code, is_tail)?;
                            
                            code.push(Opcode::Match {
                                pattern: items[2].clone(),
                                body_code: std::sync::Arc::from(body_code),
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
                                body_code: std::sync::Arc::from(body_code),
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
                                body_code: std::sync::Arc::from(body_code),
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "map-atom" if items.len() == 4 => {
                            // ponytail: map-atom Form 2 (with variable name and body expression).
                            // Simple variable → optimized MapAtomLambda opcode.
                            // Compound pattern → fallback to EvalCEK (CEK handles destructuring via try_match_one).
                            match &items[2] {
                                Expr::Symbol(var_name) => {
                                    self.compile(&items[1], code, false)?;
                                    let mut body_comp = VMCompiler {
                                        locals: self.locals.clone(),
                                        free_vars: self.free_vars.clone(),
                                        fn_name: self.fn_name.clone(),
                                        arity: self.arity,
                                    };
                                    body_comp.locals.push(var_name.clone());
                                    let mut body_code = Vec::new();
                                    body_comp.compile(&items[3], &mut body_code, false)?;

                                    for v in &body_comp.free_vars {
                                        if !self.free_vars.contains(v) {
                                            self.free_vars.push(v.clone());
                                        }
                                    }
                                    code.push(Opcode::MapAtomLambda {
                                        var_name: var_name.clone(),
                                        body_code: std::sync::Arc::from(body_code),
                                        free_vars_map: body_comp.free_vars,
                                    });
                                    return Ok(());
                                }
                                _ => {
                                    code.push(Opcode::EvalCEK(expr.clone(), self.locals.clone()));
                                    return Ok(());
                                }
                            }
                        }
                        "filter-atom" if items.len() == 4 => {
                            // ponytail: filter-atom Form 2 (with variable name and condition expression).
                            // Simple variable → optimized FilterAtomLambda opcode.
                            // Compound pattern → fallback to EvalCEK.
                            match &items[2] {
                                Expr::Symbol(var_name) => {
                                    self.compile(&items[1], code, false)?;
                                    let mut body_comp = VMCompiler {
                                        locals: self.locals.clone(),
                                        free_vars: self.free_vars.clone(),
                                        fn_name: self.fn_name.clone(),
                                        arity: self.arity,
                                    };
                                    body_comp.locals.push(var_name.clone());
                                    let mut body_code = Vec::new();
                                    body_comp.compile(&items[3], &mut body_code, false)?;

                                    for v in &body_comp.free_vars {
                                        if !self.free_vars.contains(v) {
                                            self.free_vars.push(v.clone());
                                        }
                                    }
                                    code.push(Opcode::FilterAtomLambda {
                                        var_name: var_name.clone(),
                                        body_code: std::sync::Arc::from(body_code),
                                        free_vars_map: body_comp.free_vars,
                                    });
                                    return Ok(());
                                }
                                _ => {
                                    code.push(Opcode::EvalCEK(expr.clone(), self.locals.clone()));
                                    return Ok(());
                                }
                            }
                        }
                        // For any other special keyword/construct (e.g. once, etc.), fallback to EvalCEK
                        "once" if items.len() == 2 => {
                            // ponytail: run body, keep first result only
                            let mut body_comp = VMCompiler { locals: self.locals.clone(), free_vars: self.free_vars.clone(), fn_name: self.fn_name.clone(), arity: self.arity };
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[1], &mut body_code, false)?;
                            for v in &body_comp.free_vars { if !self.free_vars.contains(v) { self.free_vars.push(v.clone()); } }
                            code.push(Opcode::Once { body_code: std::sync::Arc::from(body_code), free_vars_map: body_comp.free_vars });
                            return Ok(());
                        }
                        "progn" if items.len() >= 2 => {
                            // ponytail: eval all, return last; compile each body separately
                            let mut bodies = Vec::new();
                            let mut fvs = self.free_vars.clone();
                            let len = items.len() - 1;
                            for (idx, item) in items[1..].iter().enumerate() {
                                let last_item = idx + 1 == len;
                                let mut bc = VMCompiler { locals: self.locals.clone(), free_vars: fvs.clone(), fn_name: self.fn_name.clone(), arity: self.arity };
                                let mut bcode = Vec::new();
                                bc.compile(item, &mut bcode, if last_item { is_tail } else { false })?;
                                for v in &bc.free_vars { if !fvs.contains(v) { fvs.push(v.clone()); } }
                                bodies.push(bcode);
                            }
                            self.free_vars = fvs.clone();
                            code.push(Opcode::Progn { bodies: bodies.into_iter().map(std::sync::Arc::from).collect(), free_vars_map: fvs });
                            return Ok(());
                        }
                        "prog1" if items.len() >= 2 => {
                            // ponytail: eval all, return first
                            let mut bodies = Vec::new();
                            let mut fvs = self.free_vars.clone();
                            for item in &items[1..] {
                                let mut bc = VMCompiler { locals: self.locals.clone(), free_vars: fvs.clone(), fn_name: self.fn_name.clone(), arity: self.arity };
                                let mut bcode = Vec::new();
                                bc.compile(item, &mut bcode, false)?;
                                for v in &bc.free_vars { if !fvs.contains(v) { fvs.push(v.clone()); } }
                                bodies.push(bcode);
                            }
                            self.free_vars = fvs.clone();
                            code.push(Opcode::Prog1 { bodies: bodies.into_iter().map(std::sync::Arc::from).collect(), free_vars_map: fvs });
                            return Ok(());
                        }
                        "chain" if items.len() >= 4 && items.len() % 2 == 0 => {
                            // ponytail: (chain e0 $v0 e1 $v1 ... body) — compile each step
                            let mut fvs = self.free_vars.clone();
                            let mut steps = Vec::new();
                            let pairs = (items.len() - 2) / 2;
                            for i in 0..pairs {
                                let expr_item = &items[1 + i * 2];
                                let var_item = &items[2 + i * 2];
                                let var_name = match var_item {
                                    Expr::Symbol(s) if s.starts_with('$') => s.clone(),
                                    _ => return Err(format!("chain: arg {} must be a $variable", 2 + i * 2)),
                                };
                                let mut bc = VMCompiler { locals: self.locals.clone(), free_vars: fvs.clone(), fn_name: self.fn_name.clone(), arity: self.arity };
                                let mut bcode = Vec::new();
                                bc.compile(expr_item, &mut bcode, false)?;
                                for v in &bc.free_vars { if !fvs.contains(v) { fvs.push(v.clone()); } }
                                steps.push((bcode, var_name));
                            }
                            let mut fc = VMCompiler { locals: self.locals.clone(), free_vars: fvs.clone(), fn_name: self.fn_name.clone(), arity: self.arity };
                            let mut final_code = Vec::new();
                            fc.compile(items.last().unwrap(), &mut final_code, is_tail)?;
                            for v in &fc.free_vars { if !fvs.contains(v) { fvs.push(v.clone()); } }
                            self.free_vars = fvs.clone();
                            code.push(Opcode::Chain {
                                steps: steps.into_iter().map(|(bc, v)| (std::sync::Arc::from(bc), v)).collect(),
                                final_code: std::sync::Arc::from(final_code),
                                free_vars_map: fvs,
                            });
                            return Ok(());
                        }
                        "within" if items.len() == 2 => {
                            // ponytail: evaluate arg, wrap all results into (within ...)
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[1], &mut body_code, false)?;
                            for v in &body_comp.free_vars {
                                if !self.free_vars.contains(v) { self.free_vars.push(v.clone()); }
                            }
                            code.push(Opcode::Within {
                                body_code: std::sync::Arc::from(body_code),
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "with_mutex" if items.len() == 3 => {
                            // ponytail: compile mutex-name arg, then run body under the named lock
                            self.compile(&items[1], code, false)?;
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[2], &mut body_code, is_tail)?;
                            for v in &body_comp.free_vars {
                                if !self.free_vars.contains(v) { self.free_vars.push(v.clone()); }
                            }
                            code.push(Opcode::WithMutex {
                                body_code: std::sync::Arc::from(body_code),
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "transaction" if items.len() == 2 => {
                            // ponytail: snapshot state, run body, rollback on empty/error
                            let mut body_comp = VMCompiler {
                                locals: self.locals.clone(),
                                free_vars: self.free_vars.clone(),
                                fn_name: self.fn_name.clone(),
                                arity: self.arity,
                            };
                            let mut body_code = Vec::new();
                            body_comp.compile(&items[1], &mut body_code, is_tail)?;
                            for v in &body_comp.free_vars {
                                if !self.free_vars.contains(v) { self.free_vars.push(v.clone()); }
                            }
                            code.push(Opcode::Transaction {
                                body_code: std::sync::Arc::from(body_code),
                                free_vars_map: body_comp.free_vars,
                            });
                            return Ok(());
                        }
                        "import!" if items.len() == 3 => {
                            // ponytail: path is always a compile-time literal; compile space-ref arg only
                            // Performance: avoids a full CEK round-trip just to eval &self
                            let path_opcode = match &items[2] {
                                // (library path.py) — Python import, space-ref is still evaluated but unused
                                Expr::List(lib) if lib.len() == 2 => {
                                    if let (Expr::Symbol(head), Expr::Symbol(py) | Expr::Str(py)) = (&lib[0], &lib[1]) {
                                        if head == "library" {
                                            Some(Opcode::PythonImport { path: py.clone() })
                                        } else { None }
                                    } else { None }
                                }
                                Expr::Symbol(p) | Expr::Str(p) => {
                                    if p.ends_with(".py") {
                                        Some(Opcode::PythonImport { path: p.clone() })
                                    } else {
                                        Some(Opcode::ImportFile { path: p.clone() })
                                    }
                                }
                                _ => None,
                            };
                            if let Some(opcode) = path_opcode {
                                self.compile(&items[1], code, false)?; // evaluate space-ref
                                code.push(opcode);
                                return Ok(());
                            }
                            // Dynamic path — fallback to EvalCEK
                            code.push(Opcode::EvalCEK(expr.clone(), self.locals.clone()));
                            return Ok(());
                        }
                        "|->" | "add-atom" | "remove-atom" => {
                            code.push(Opcode::EvalCEK(expr.clone(), self.locals.clone()));
                            return Ok(());
                        }
                        "py-call" if items.len() == 2 => {
                            // Compile py-call expression directly — avoids CEK round-trip.
                            // The Python expression tree is not evaluated as MeTTa args;
                            // `expr_to_py` resolves $var references at runtime from the env.
                            code.push(Opcode::PyCall { expr: items[1].clone() });
                            return Ok(());
                        }
                        "py-eval" if items.len() == 2 => {
                            // py-eval takes a Python code string; keep as CEK fallback (infrequent).
                            // ponytail: not worth a dedicated opcode — rare in hot paths.
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
                                code.push(Opcode::TailCallSelf);
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
            body_code: std::sync::Arc::from(body_code),
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
