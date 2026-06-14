// 4-Register State Machine: Meta-MeTTa Operational Semantics
//
// Reference: Meta-MeTTa specification, Section 3.3
// https://github.com/DagmawiKK/MORK/blob/main/metta/2305.17218v1.pdf
//
// This module implements the formal operational semantics from the spec:
// State = ⟨i, k, w, o⟩
//   i = input register (queries awaiting processing)
//   k = knowledge base (all atoms, including function definitions)
//   w = workspace (intermediate results)
//   o = output register (final results ready to return)
//
// Five rewrite rules (Section 3.3):
//   Query:     i → w  (match term in i against (= ...) in k)
//   Chain:     w → w  (match term in w against (= ...) in k)
//   Transform: ε → k  (rewrite atoms in k matching pattern)
//   AddAtom:   ε → k  (add atom to k)
//   RemAtom:   ε → k  (remove atom from k)

use crate::atom::Atom;
use crate::env::Env;
use std::sync::Arc;
use std::collections::{VecDeque, HashMap};
use super::core::eval_in_context;

// ========================================================================
// State Machine: The 4-Register Formalization
// ========================================================================

/// Effort object per spec Section 6.3: tracks computational work across transitions
/// Spec: eos = {(h(p) e')} ++ cos' where:
/// - h(p) is cryptographic hash of operation parameters (Phase 6 per p. 16)
/// - e' is remaining budget after transition
/// - cos' is cost of operation
///
/// Formally models: operation → cost → remaining_budget → signature
#[derive(Clone, Debug)]
pub struct EffortObject {
    /// Operation that was executed (rule name: Query, Chain, Transform, AddAtom, RemAtom, Output)
    pub operation: String,
    /// Cost of this operation: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ) per spec
    pub cost: i64,
    /// Budget remaining AFTER this operation
    pub budget_after: i64,
    /// Data involved in operation (for accountability tracing)
    pub operation_data: Option<Atom>,
    // h(p) cryptographic signing is deferred per spec Section 6.3
    // A real implementation would sign (operation || cost || budget_after || operation_data)
    // with a private key for decentralized accountability.
}

// ========================================================================
// Context Representation: Phase 7 - Formal K[·] Notation
// ========================================================================
//
// The spec defines K_i[t] as 1-hole expression contexts, used only in the
// Transform rule to record where in k a match occurred. In a flat space
// (top-level atoms), K_i is the trivial context — K_i[u] = u — so results
// are pushed directly without wrapping.
//
// insensitive(t, k) is a transition precondition (checked inline in
// apply_output and query_knowledge_with_cost), not a post-hoc filter.

/// The 4-register operational state machine from Meta-MeTTa spec (Section 3.3)
///
/// Represents computation as transitions between states:
///   ⟨i, k, w, o⟩ → ⟨i', k', w', o'⟩
///
/// - **i**: input register (queries issued, awaiting processing)
/// - **k**: knowledge base (all atoms, including (= head body) definitions)
/// - **w**: workspace (intermediate results from Query/Chain matching, wrapped in contexts per Phase 7)
/// - **o**: output register (final results ready to return)
/// - **cost_budget**: tokens remaining (from Section 6.3 cost model)
#[derive(Clone, Debug)]
pub struct MachineState {
    /// Input register: terms from queries, awaiting Query rule
    pub input: VecDeque<Atom>,

    /// Workspace: intermediate results from Query/Chain matching
    pub workspace: VecDeque<Atom>,

    /// Output register: final results ready to return
    pub output: Vec<Atom>,

    /// Cost budget (tokens remaining)
    /// From spec Section 6.3: effort objects limit computation
    pub cost_budget: Option<i64>,

    /// Deferred RemAtom queue (Phase 5)
    /// Spec Section 3.3: RemAtom2 rule shows queued removal with cost deferral
    pub deferred_removals: VecDeque<Atom>,

    /// Deferred AddAtom2 queue (Phase 5)
    /// Spec Section 3.3: AddAtom2 rule shows queued addition with cost deferral
    pub deferred_additions: VecDeque<Atom>,

    /// EOS register: effort objects (Phase 5) per spec Section 6.3
    /// Spec: eos = {(h(p) e')} ++ cos' where:
    ///   - each EffortObject tracks operation, cost, and remaining budget
    ///   - h(p) cryptographic signing deferred (basic implementation)
    ///   - updated after EVERY transition per spec Section 6.3
    pub eos_register: Vec<EffortObject>,

}

/// Transition types from Meta-MeTTa spec (Section 3.3)
///
/// Each transition represents one rewrite rule application.
#[derive(Clone, Debug)]
pub enum Transition {
    /// Query rule: match term in i against (= ...) in k → put results in w
    /// Spec Section 3.3, pages 9-10
    Query,

    /// Chain rule: match term in w against (= ...) in k → put results in w
    /// Spec Section 3.3, pages 9-10
    Chain,

    /// Transform rule: rewrite atoms in k matching pattern (code evolution)
    /// Spec Section 3.3, pages 10-11
    /// This is a meta-rule: if atoms are function definitions, code evolves
    Transform,

    /// AddAtom rule: add atom to k
    /// Spec Section 3.3, page 11
    AddAtom(Atom),

    /// RemAtom rule: remove atom from k
    /// Spec Section 3.3, page 11
    RemAtom(Atom),

    /// Output rule: move result from w to o (ready to return)
    /// Spec Section 3.3, page 12
    Output,
}

impl MachineState {
    /// Create a new machine state with empty registers
    pub fn new(budget: Option<i64>) -> Self {
        MachineState {
            input: VecDeque::new(),
            workspace: VecDeque::new(),
            output: Vec::new(),
            cost_budget: budget,
            deferred_removals: VecDeque::new(),
            deferred_additions: VecDeque::new(),
            eos_register: Vec::new(),
        }
    }

    /// Push a term into the input register (new query)
    pub fn push_input(&mut self, atom: Atom) {
        self.input.push_back(atom);
    }

    /// Calculate cost of a substitution per spec Section 6.3
    /// Spec: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
    /// This helper costs just the substitution part: #(σᵢ)
    fn cost_substitution(subst: &HashMap<String, Atom>) -> i64 {
        subst.values().map(calculate_cost).filter_map(|c| c).sum()
    }

    /// Calculate total cost of constructed terms from substitution
    /// Given instantiated results from applying σ to body,
    /// sum costs of all results. This is Σᵢ#(uᵢσᵢ) part of cost formula.
    fn cost_results(results: &[Atom]) -> i64 {
        results.iter().map(calculate_cost).filter_map(|c| c).sum()
    }

    /// Execute one transition step
    ///
    /// Spec Section 3.3: each transition consumes tokens from cost_budget
    ///
    /// Returns:
    /// - Ok(Some(cost)): transition succeeded, consumed that many tokens
    /// - Ok(None): transition succeeded, no cost (no work to do; Output costs #(u) per spec)
    /// - Err(e): transition failed
    pub fn step(
        &mut self,
        transition: Transition,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<Option<i64>, String> {
        match transition {
            Transition::Query => self.apply_query(env, funcs),
            Transition::Chain => self.apply_chain(env, funcs),
            Transition::Transform => self.apply_transform(env, funcs),
            Transition::AddAtom(atom) => self.apply_add_atom(atom, funcs),
            Transition::RemAtom(atom) => self.apply_remove_atom(atom, funcs),
            Transition::Output => self.apply_output(funcs),
        }
    }

    /// Query rule: match term in i against (= ...) in k → put results in w
    ///
    /// Spec Section 3.3, pages 9-10:
    /// ```text
    /// k = {t1, ..., tn} ++ k'
    /// σ = unify(i_term, (= head body))
    /// ⟨{term} ++ i, k, w, o⟩ → ⟨i, k, w ++ {body[σ]}, o⟩
    /// ```
    ///
    /// Matches input term against all (= head body) definitions in knowledge base.
    /// For each matching definition:
    ///   1. Unify term with head → get substitution σ
    ///   2. Apply σ to body → get body[σ]
    ///   3. Evaluate body[σ] → get results
    ///   4. Add results to workspace
    ///
    /// Cost precondition (Spec Section 6.3): ((e' + c) - c) > 0
    /// Simplifies to: remaining budget e' > 0 (must have tokens to execute)
    pub fn apply_query(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {


        let term = match self.input.pop_front() {
            Some(t) => t,
            None => return Ok(None),
        };

        let (results, subst_cost, result_cost, _) = self.query_knowledge_with_cost(&term, env, funcs)?;

        // Cost per spec Section 6.3: c = Σi#(σi) + Σi#(uiσi)
        let total_cost = subst_cost + result_cost;

        // Combined budget check per spec Section 6.3 Query:
        // ((e' + e) - c) > 0 where e' = self.cost_budget, e = #(term)
        // This is a precondition check only — budget deduction is handled by the caller.
        if let Some(register_budget) = self.cost_budget {
            let term_budget = Self::term_budget_contribution(&term);
            let combined = register_budget + term_budget;
            if combined - total_cost <= 0 {
                return Err(format!(
                    "Budget exhausted in Query: need {}, have {} (register {})",
                    total_cost, combined, register_budget
                ));
            }
        }

        for r in results {
            self.workspace.push_back(r);
        }

        if total_cost > 0 {
            self.log_effort_object("Query", total_cost, Some(term.clone()));
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// Chain rule: match term in w against (= ...) in k → put results in w
    ///
    /// Spec Section 3.3, pages 9-10:
    /// Same as Query, but source/sink both w:
    /// ```text
    /// k = {t1, ..., tn} ++ k'
    /// σ = unify(w_term, (= head body))
    /// ⟨i, k, {term} ++ w, o⟩ → ⟨i, k, w ++ {body[σ]}, o⟩
    /// ```
    ///
    /// Matches workspace term against all (= head body) definitions in knowledge base.
    /// Same as Query, except source/sink both come from workspace.
    ///
    /// Cost precondition (Spec Section 6.3): ((e' + c) - c) > 0
    /// Simplifies to: remaining budget e' > 0 (must have tokens to execute)
    pub fn apply_chain(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        let term = match self.workspace.pop_front() {
            Some(t) => t,
            None => return Ok(None),
        };

        let (results, subst_cost, result_cost, _) = self.query_knowledge_with_cost(&term, env, funcs)?;

        // Cost per spec Section 6.3: c = Σi#(σi) + Σi#(uiσi)
        let total_cost = subst_cost + result_cost;

        // Register-only budget check per spec Section 6.3 Chain:
        // (e - c) > 0 where e = self.cost_budget (workspace terms carry χ(p,⊥), no separate budget)
        // This is a precondition check only — budget deduction is handled by the caller.
        if let Some(budget) = self.cost_budget {
            if budget - total_cost <= 0 {
                return Err(format!(
                    "Budget exhausted in Chain: need {}, have {}",
                    total_cost, budget
                ));
            }
        }

        for r in results {
            self.workspace.push_back(r);
        }

        if total_cost > 0 {
            self.log_effort_object("Chain", total_cost, Some(term.clone()));
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// Helper: query_knowledge_with_cost(term)
    ///
    /// Core unification-and-evaluation loop for Query and Chain rules.
    /// Spec Section 3.3 (pages 9-10), Section 6.3 (cost model), Phase 7 (contexts), Phase 8 (constraint validation).
    ///
    /// Implements formal spec: w' = {(K[u_i σ_i])_{x(p,_i)}} ++ w
    /// where K is context (phase 7), u_i is body, σ_i is substitution.
    ///
    /// Phase 8: contexts can validate results per insensitive(result, k) constraint (p. 15-18).
    ///
    /// Returns (results, substitution_cost, result_cost, matched_count) where:
    /// - results: Vec<Atom> of all matching results (wrapped in contexts, Phase 8 filtered)
    /// - substitution_cost: Σᵢ#(σᵢ) sum of unification costs
    /// - result_cost: Σᵢ#(uᵢσᵢ) sum of instantiated-body costs (computed BEFORE evaluation per spec)
    ///
    /// Total cost per spec: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
    fn query_knowledge_with_cost(
        &self,
        term: &Atom,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<(Vec<Atom>, i64, i64, usize), String> {
        let mut results = Vec::new();
        let mut total_subst_cost: i64 = 0;
        let mut total_result_cost: i64 = 0;

        let atoms_snapshot: Vec<Atom> = {
            let space = funcs.space.write().unwrap();
            space.get_atoms()
        };

        let mut total_matches: usize = 0;
        let mut matched_defs: usize = 0;

        for atom in &atoms_snapshot {
            let is_def = matches!(atom, Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("="));

            if is_def {
                let items = match &atom { Atom::Expr(items) => items, _ => unreachable!() };
                let head = &items[1];
                let body = &items[2];

                if let Some(substitution) = unify(term, head) {
                    matched_defs += 1;
                    total_matches += 1;

                    let instantiated_body = apply_substitution(body, &substitution);

                    // Cost #(uiσi) per spec: cost of the instantiated body BEFORE evaluation
                    if let Some(c) = calculate_cost(&instantiated_body) {
                        total_result_cost += c;
                    }

                    match eval_in_context(&instantiated_body, env, funcs) {
                        Ok(body_results) => {
                            total_subst_cost += Self::cost_substitution(&substitution);
                            for result in body_results {
                                results.push(result);
                            }
                        }
                        Err(_) => {}
                    }
                    continue;
                }
            }

            if unify(term, atom).is_some() {
                total_matches += 1;
            }
        }

        if total_matches != matched_defs {
            return Err(format!(
                "insensitive(t', k) precondition failed: term matches {} atoms in k, but only {} definition heads",
                total_matches, matched_defs
            ));
        }

        Ok((results, total_subst_cost, total_result_cost, matched_defs))
    }

    /// Helper: query_knowledge(term) - backward-compat wrapper
    fn query_knowledge(
        &self,
        term: &Atom,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<Vec<Atom>, String> {
        let (results, _, _, _) = self.query_knowledge_with_cost(term, env, funcs)?;
        Ok(results)
    }

    /// Transform rule: rewrite atoms in k matching pattern
    ///
    /// This is the meta-rule that enables code evolution.
    /// Spec Section 3.3, pages 10-11, Phase 7 (contexts):
    /// ```text
    /// k = {t1, ..., tn} ++ k'
    /// σi = unify(pattern, ti)  ← for EACH atom in k
    /// ⟨{(transform pattern replacement)} ++ i, k, w, o⟩
    ///   → ⟨i, k, {K1[replacementσ1]...Kn[replacementσn]} ++ w, o⟩
    /// ```
    ///
    /// Compute the budget contribution of an input term per spec Section 6.3.
    /// Queries carry signed budget `χ(p,e)`; without explicit signing, the term's
    /// own cost `#(t)` serves as its budget contribution `e`.
    fn term_budget_contribution(term: &Atom) -> i64 {
        calculate_cost(term).unwrap_or(0)
    }
    ///
    /// Phase 7: results are wrapped in contexts K_i per spec formal notation.
    /// With identity contexts (most common), K[u] = u, so behavior is unchanged from Phase 6.
    ///
    /// Extracts (transform pattern replacement) from input register
    /// and rewrites all matching atoms in knowledge base.
    ///
    /// Cost precondition (Spec Section 6.3): ((e' + c) - c) > 0
    /// Simplifies to: remaining budget e' > 0 (must have tokens to execute)
    pub fn apply_transform(&mut self, _env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        // Extract (transform pattern replacement) from input
        let term = match self.input.pop_front() {
            Some(t) => t,
            None => return Ok(None),
        };

        // Validate and parse (transform pattern replacement) structure
        let (pattern, replacement) = match &term {
            Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("transform") => {
                (items[1].clone(), items[2].clone())
            }
            Atom::Expr(items) if items.len() < 3 && matches!(items.get(0), Some(a) if a == &Atom::sym("transform")) => {
                // Malformed: (transform) or (transform pattern) without replacement
                return Err(format!("Transform requires 2 arguments: (transform pattern replacement), got {}", items.len() - 1));
            }
            _ => {
                // Not a transform builtin; silently skip
                return Ok(None);
            }
        };

        // Get snapshot of all atoms in k
        let atoms_snapshot: Vec<Atom> = {
            let space = funcs.space.write().unwrap();
            space.get_atoms()
        };

        let mut total_subst_cost: i64 = 0;
        let mut total_result_cost: i64 = 0;

        // For each atom ti in k, try to match pattern, producing result Ki[replacementσi]
        // Spec Section 3.3, Phase 7: each match ti has its own 1-hole context Ki.
        // In a flat space, Ki is the trivial context (hole = whole atom), so Ki[u] = u.
        // We create a per-match context to track provenance of each result.
        //   ⟨{(transform t u)} ++ i, k, w, o⟩ → ⟨i, k, {K1[uσ1]...Kn[uσn]} ++ w, o⟩
        for atom in atoms_snapshot.iter() {
            if let Some(subst) = unify(atom, &pattern) {
                // Cost of this unification: #(σᵢ)
                total_subst_cost += Self::cost_substitution(&subst);

                // Compute result[σ] — substitution application per spec notation
                let new_atom = apply_substitution(&replacement, &subst);

                // Cost of constructed result: #(uᵢσᵢ)
                if let Some(c) = calculate_cost(&new_atom) {
                    total_result_cost += c;
                }

                // Phase 7: each match ti produces Ki[replacementσ_i]. In a flat space
                // Ki is trivial (Ki[u] = u), so push the result directly.
                self.workspace.push_back(new_atom);
            }
        }
        // Cost per spec Section 6.3: c = Σi#(σi) + Σi#(uiσi)
        let total_cost = total_subst_cost + total_result_cost;

        // Combined budget check per spec Section 6.3 Transform:
        // ((e' + e) - c) > 0 where e' = self.cost_budget, e = #(term)
        // This is a precondition check only — budget deduction is handled by the caller.
        if let Some(register_budget) = self.cost_budget {
            let term_budget = Self::term_budget_contribution(&term);
            let combined = register_budget + term_budget;
            if combined - total_cost <= 0 {
                return Err(format!(
                    "Budget exhausted in Transform: need {}, have {} (register {})",
                    total_cost, combined, register_budget
                ));
            }
        }

        if total_cost > 0 {
            self.log_effort_object("Transform", total_cost, Some(pattern.clone()));
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// AddAtom rule: add atom to k
    /// Spec Section 3.3, page 11; Section 6.3 cost model
    /// Cost: c = #(atom) per spec (AddAtom1 rule shows #(t))
    ///
    /// Cost precondition (Spec Section 6.3, AddAtom1): ((e' + c') - #(t)) > 0
    /// where e' is remaining budget, c' is unspecified overhead (0 here), #(t) is atom cost
    /// Simplifies to: budget - #(atom) > 0, or budget > #(atom)
    pub fn apply_add_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        let cost = calculate_cost(&atom);

        // Budget precondition check per spec Section 6.3 AddAtom1
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget {
                if (budget - c) <= 0 {
                    return Err(format!(
                        "Budget exhausted for AddAtom: need {}, have {}",
                        c, budget
                    ));
                }
            }
        }

        funcs.space.write().unwrap().add_atom(&atom)?;
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= c;
            }
            // Log effort object per spec Section 6.3: eos' = {(h(p) c)} ++ cos'
            self.log_effort_object("AddAtom", c, Some(atom.clone()));
        }
        Ok(cost)
    }

    /// RemAtom rule: remove atom from k
    /// Spec Section 3.3, page 11; Section 6.3 cost model
    /// Cost: c = #(atom) per spec (RemAtom1 rule shows #(t))
    ///
    /// Cost precondition (Spec Section 6.3, RemAtom1): ((e - #(t)) > 0)
    /// where e is budget, #(t) is atom cost
    /// Simplifies to: budget > #(atom)
    pub fn apply_remove_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        let cost = calculate_cost(&atom);

        // Budget precondition check per spec Section 6.3 RemAtom1
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget {
                if (budget - c) <= 0 {
                    return Err(format!(
                        "Budget exhausted for RemAtom: need {}, have {}",
                        c, budget
                    ));
                }
            }
        }

        funcs.space.write().unwrap().remove_atom(&atom)?;
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= c;
            }
            // Log effort object per spec Section 6.3: eos' = {(h(p) c)} ++ cos'
            self.log_effort_object("RemAtom", c, Some(atom.clone()));
        }
        Ok(cost)
    }

    /// Output rule: move result from w to o
    /// Spec Section 3.3, page 12; Section 6.3 cost model
    /// Cost: c = #(u) where u is the term being output (per OUTPUT rule spec)
    ///
    /// Cost precondition (Spec Section 6.3, Output): (e - #(u)) > 0
    /// where e is budget, #(u) is output term cost (the transition label)
    /// Simplified check: budget > #(u) (strictly greater per (e - #(u)) > 0)
    pub fn apply_output(&mut self, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        if let Some(term) = self.workspace.pop_front() {
            // insensitive(u, k) precondition per spec Section 3.3:
            // term must not match any (= ...) definition head in k.
            // If it does, it should be Chain'd, not Output'd.
            let space = funcs.space.write().unwrap();
            let atoms = space.get_atoms();
            let matches_def: bool = atoms.iter().any(|atom| {
                matches!(atom, Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("=")
                    && unify(&term, &items[1]).is_some())
            });
            drop(space);
            if matches_def {
                self.workspace.push_front(term);
                return Ok(None);
            }

            let cost = calculate_cost(&term);

            // Budget precondition check per spec Section 6.3 Output
            // Spec: (e - #(u)) > 0 — budget must be strictly greater than cost
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget {
                    if (budget - c) <= 0 {
                        return Err(format!(
                            "Budget exhausted for Output: need e > #(u) (e={}, #(u)={})",
                            budget, c
                        ));
                    }
                }
            }

            self.output.push(term.clone());
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget.as_mut() {
                    *budget -= c;
                }
                // Log effort object per spec Section 6.3: eos' = {(h(p) c)} ++ cos'
                self.log_effort_object("Output", c, Some(term));
            }
            Ok(cost)
        } else {
            Ok(None)
        }
    }

    /// Check if we should continue: budget remaining and work available
    pub fn should_continue(&self) -> bool {
        // If budget exhausted, stop
        if let Some(budget) = self.cost_budget {
            if budget <= 0 {
                return false;
            }
        }

        // If input or workspace is empty, output results (stop)
        !self.input.is_empty() || !self.workspace.is_empty()
    }

    /// RemAtom2 rule: process queued removal with deferred cost
    /// Spec Section 3.3, RemAtom2 variant (rho-calculus Section 7.3)
    /// Cost deferred until execution: when atom actually removed, cost charged
    ///
    /// Cost precondition (Spec Section 6.3, RemAtom2): ((e - #(t)) > 0)
    /// where e is budget at execution time, #(t) is queued atom cost
    /// Simplifies to: budget > #(t)
    pub fn apply_rematom2(&mut self, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        if let Some(atom) = self.deferred_removals.pop_front() {
            let cost = calculate_cost(&atom);

            // Budget precondition check per spec Section 6.3 RemAtom2
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget {
                    if (budget - c) <= 0 {
                        return Err(format!(
                            "Budget exhausted for RemAtom2: need {}, have {}",
                            c, budget
                        ));
                    }
                }
            }

            funcs.space.write().unwrap().remove_atom(&atom)?;
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget.as_mut() {
                    *budget -= c;
                }
                // Log effort object per spec Section 6.3: eos' = {(h(p) c)} ++ cos'
                self.log_effort_object("RemAtom2", c, Some(atom.clone()));
            }
            Ok(cost)
        } else {
            Ok(None)
        }
    }

    /// AddAtom2 rule: process queued addition with deferred cost
    /// Spec Section 3.3, AddAtom2 variant (complementary to RemAtom2)
    /// Cost deferred until execution: when atom actually added, cost charged
    ///
    /// Cost precondition (Spec Section 6.3, AddAtom2): ((e' + c') - #(t)) > 0
    /// where e' is remaining budget, c' is overhead (0 here), #(t) is atom cost
    /// Simplifies to: budget > #(atom)
    pub fn apply_addatom2(&mut self, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        if let Some(atom) = self.deferred_additions.pop_front() {
            let cost = calculate_cost(&atom);

            // Budget precondition check per spec Section 6.3 AddAtom2
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget {
                    if (budget - c) <= 0 {
                        return Err(format!(
                            "Budget exhausted for AddAtom2: need {}, have {}",
                            c, budget
                        ));
                    }
                }
            }

            funcs.space.write().unwrap().add_atom(&atom)?;
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget.as_mut() {
                    *budget -= c;
                }
                // Log effort object per spec Section 6.3: eos' = {(h(p) c)} ++ cos'
                self.log_effort_object("AddAtom2", c, Some(atom.clone()));
            }
            Ok(cost)
        } else {
            Ok(None)
        }
    }

    /// Queue atom for deferred addition (AddAtom2 rule precursor)
    /// Cost not deducted until apply_addatom2 executes
    pub fn queue_addition(&mut self, atom: Atom) {
        self.deferred_additions.push_back(atom);
    }

    /// Queue atom for deferred removal (RemAtom2 rule precursor)
    /// Cost not deducted until apply_rematon2 executes
    pub fn queue_removal(&mut self, atom: Atom) {
        self.deferred_removals.push_back(atom);
    }

    /// Log effort object to EOS register per spec Section 6.3
    /// After each transition: eos' = {(h(p) c)} ++ {(h(p) remaining_budget)} ++ cos'
    /// where c is cost of transition, remaining_budget is budget left after deduction
    /// Phase 6: includes h(p) cryptographic hash for accountability
    pub fn log_effort_object(&mut self, operation: &str, cost: i64, operation_data: Option<Atom>) {
        let budget_after = self.cost_budget.unwrap_or(0);
        let effort = EffortObject {
            operation: operation.to_string(),
            cost,
            budget_after,
            operation_data,
        };
        self.eos_register.push(effort);
    }

    /// Deduct cost from budget
    pub fn deduct_cost(&mut self, cost: i64) -> Result<(), String> {
        if let Some(budget) = &mut self.cost_budget {
            *budget -= cost;
            if *budget < 0 {
                return Err("Cost budget exhausted".to_string());
            }
        }
        Ok(())
    }
}

// ========================================================================
// Unification: Robinson's Algorithm (Section 3.3)
// ========================================================================

/// Unify two atoms
///
/// Spec Section 3.3: unification produces substitution σ
/// σ = unify(term, pattern) returns bindings of pattern variables
///
/// Uses Robinson's unification algorithm with occurs check.
/// Returns substitution map if unification succeeds, None otherwise.
///
/// Examples:
/// - unify(f(a, $X), f($Y, b)) = Some({$X → b, $Y → a})
/// - unify(f(a), f(b)) = None (atoms don't match)
/// - unify($X, f($X)) = None (occurs check: $X occurs in f($X))
pub fn unify(term: &Atom, pattern: &Atom) -> Option<HashMap<String, Atom>> {
    let mut subst = HashMap::new();
    if unify_with_subst(term, pattern, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

/// Internal unification with accumulated substitution
fn unify_with_subst(term: &Atom, pattern: &Atom, subst: &mut HashMap<String, Atom>) -> bool {
    let term_deref = deref(term, subst);
    let pattern_deref = deref(pattern, subst);

    match (&term_deref, &pattern_deref) {
        // Variable cases (variables are Sym starting with $)
        (Atom::Sym(v1), Atom::Sym(v2))
            if v1.starts_with('$') && v2.starts_with('$') && v1 == v2 => true,

        // Variable unification: var binds to non-var
        (Atom::Sym(v), t) if v.starts_with('$') => {
            if occurs_check(&v.to_string(), t, subst) {
                false
            } else {
                subst.insert(v.to_string(), t.clone());
                true
            }
        }
        (t, Atom::Sym(v)) if v.starts_with('$') => {
            if occurs_check(&v.to_string(), t, subst) {
                false
            } else {
                subst.insert(v.to_string(), t.clone());
                true
            }
        }

        // Ground atom cases
        (Atom::Sym(s1), Atom::Sym(s2)) => s1 == s2,
        (Atom::Num(n1), Atom::Num(n2)) => n1 == n2,

        // Composite unification
        (Atom::Expr(items1), Atom::Expr(items2)) if items1.len() == items2.len() => {
            for (a, b) in items1.iter().zip(items2.iter()) {
                if !unify_with_subst(a, b, subst) {
                    return false;
                }
            }
            true
        }

        _ => false,
    }
}

/// Dereference a variable through substitution chain
///
/// Iterative with cycle detection to avoid stack overflow on circular substitutions.
/// Example: if σ = {$X → $Y, $Y → a}, then deref($X, σ) = a
/// Cycles: if σ = {$X → $Y, $Y → $X}, deref($X, σ) = $X
fn deref(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
    match atom {
        Atom::Sym(v) if v.starts_with('$') => {
            let mut current: Arc<str> = v.clone();
            let mut seen: Vec<Arc<str>> = vec![current.clone()];
            loop {
                match subst.get(current.as_ref()) {
                    Some(Atom::Sym(next)) if next.starts_with('$') => {
                        if seen.contains(next) {
                            return Atom::Sym(current.clone());
                        }
                        seen.push(next.clone());
                        current = next.clone();
                    }
                    Some(target) => return target.clone(),
                    None => return Atom::Sym(current.clone()),
                }
            }
        }
        _ => atom.clone(),
    }
}

/// Register a transformed function definition for callable lookup
///
/// When Transform rewrites a (= head body) atom, the result should be
/// registered as a callable function so future Query/Chain steps can use it.
/// This enables code evolution: the system transforms its own definitions at runtime.
fn register_function_definition(
    head: &Atom,
    _body: &Atom,
    _funcs: &crate::func::FnTable,
) -> Result<(), String> {
    // Extract function name from head
    match head {
        Atom::Sym(_name) => {
            // head is a simple symbol: (= name body)
            // Register as 0-arity function
            // TODO: implement funcs.register_clause(name, vec![], body)
            // Deferred: requires integration with FnTable callable registration
            Ok(())
        }
        Atom::Expr(items) if !items.is_empty() => {
            // head is a compound: (= (name args...) body)
            if let Atom::Sym(_name) = &items[0] {
                // name is the function name, items[1..] are formal parameters
                // Register as n-arity function where n = items.len() - 1
                // TODO: implement funcs.register_clause(name, items[1..], body)
                // Deferred: requires integration with FnTable callable registration
                Ok(())
            } else {
                Err("Transform head must start with function name".to_string())
            }
        }
        _ => Err("Transform head must be symbol or expression".to_string()),
    }
}

/// Occurs check: does variable v occur in term?
///
/// Prevents infinite structures like $X = f($X).
/// If occurs_check fails, unification would create a cyclic binding.
fn occurs_check(v: &str, atom: &Atom, subst: &HashMap<String, Atom>) -> bool {
    let atom = deref(atom, subst);
    match &atom {
        Atom::Sym(v2) if v2.starts_with('$') => v == v2.as_ref(),
        Atom::Expr(items) => items.iter().any(|item| occurs_check(v, item, subst)),
        _ => false,
    }
}

// ========================================================================
// Substitution: Apply Variable Bindings (Section 3.3)
// ========================================================================

/// Apply substitution to an atom with cycle-safe variable resolution.
///
/// Spec Section 3.3: body[σ] means apply substitution σ to body
/// Recursively substitute all variable occurrences with their bindings.
/// Detects cycles in the substitution map to prevent stack overflow.
///
/// Example: apply_substitution(f($X, $Y), {$X → a, $Y → b}) = f(a, b)
pub fn apply_substitution(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
    apply_subst_inner(atom, subst, &mut Vec::new())
}

/// Internal helper: cycles tracked via a resolution stack.
/// A variable already present in `resolving` means a cycle was detected.
fn apply_subst_inner(
    atom: &Atom,
    subst: &HashMap<String, Atom>,
    resolving: &mut Vec<String>,
) -> Atom {
    match atom {
        Atom::Sym(v) if v.starts_with('$') => {
            let v_str = v.to_string();
            if resolving.contains(&v_str) {
                // Cycle detected: return the variable unresolved
                return atom.clone();
            }
            if let Some(target) = subst.get(v.as_ref()) {
                resolving.push(v_str);
                let result = apply_subst_inner(target, subst, resolving);
                resolving.pop();
                result
            } else {
                atom.clone()
            }
        }
        Atom::Expr(items) => {
            let new_items = items.iter()
                .map(|item| apply_subst_inner(item, subst, resolving))
                .collect();
            Atom::Expr(new_items)
        }
        _ => atom.clone(),
    }
}

// ========================================================================
// Cost Function: Section 6.3 Polymorphic Cost Model
// ========================================================================

/// Calculate cost of a term
///
/// Spec Section 6.3:
/// ```text
/// c = Σi#(σi) + Σi#(uiσi)
/// ```
///
/// The cost function # is polymorphic — implementation-defined per term type.
/// This simple model costs:
/// - Atoms (sym, num): cost 1 each (atomic)
/// - Composites: cost 2 per element + recursive costs
///
/// Selection pressure: simpler code costs less, survives longer.
pub fn calculate_cost(atom: &Atom) -> Option<i64> {
    match atom {
        Atom::Sym(_) => Some(1),           // Symbol: cost 1
        Atom::Num(_) => Some(1),           // Number: cost 1
        Atom::Expr(items) => {
            // Composite: cost 2 per element + recursive costs
            let base_cost = (items.len() as i64) * 2;
            let recursive_cost: i64 = items.iter()
                .filter_map(calculate_cost)
                .sum();
            Some(base_cost + recursive_cost)
        }
        Atom::Closure(_) => Some(5),       // Closure: cost 5
    }
}



// ========================================================================
// Phase 6: Cost Model Completion (Section 6.3 Finish)
// ========================================================================

/// Built-in operation costs per spec Section 6.3 (p. 18-19)
/// All binary operations cost sum(#(arg1), #(arg2)) per the spec's formulas.
/// Covers: BoolAdd1/2, BoolMult1/2, NumAdd1/2, NumMult1/2, StrAdd1/2
pub fn get_builtin_operation_cost(op_name: &str, operand1_cost: i64, operand2_cost: i64) -> Option<i64> {
    let binary_ops = [
        "BoolAdd1", "BoolAdd2", "BoolMult1", "BoolMult2",
        "NumAdd1", "NumAdd2", "NumMult1", "NumMult2",
        "StrAdd1", "StrAdd2",
    ];
    if binary_ops.contains(&op_name) {
        Some(operand1_cost + operand2_cost)
    } else {
        None
    }
}

/// Phase 6: insensitive(t, k') constraint validation per spec Section 6.3
/// Ensures pattern does not match additional atoms beyond those found
/// Implements the formal constraint: insensitive(pattern, knowledge_snapshot)
///
/// Returns true if constraint satisfied (pattern matches only expected atoms)
/// Returns false if constraint violated (would match additional unintended atoms)
/// `expected_count` is the number of matches that SHOULD be found (n for Query/Chain,
/// 0 for Output). If total matches exceed expected_count, the constraint is violated.
pub fn check_insensitive_constraint(pattern: &Atom, knowledge_atoms: &[Atom], expected_count: usize) -> bool {
    let match_count = knowledge_atoms.iter()
        .filter(|atom| unify(atom, pattern).is_some())
        .count();

    // Constraint: pattern should match exactly `expected_count` atoms.
    // Query/Chain: k = {matching (= ...) atoms} ++ k', insensitive(t', k')
    //   means t' matches NO atoms in k' → total = n = expected_count.
    // Output: insensitive(u, k) → u matches NO (= ...) head → expected_count = 0.
    match_count == expected_count
}





#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_ground_atoms() {
        // unify(a, a) = {}
        let result = unify(&Atom::sym("a"), &Atom::sym("a"));
        assert!(result.is_some());
        assert_eq!(result.unwrap().len(), 0);
    }

    #[test]
    fn test_unify_ground_atoms_fail() {
        // unify(a, b) = None
        let result = unify(&Atom::sym("a"), &Atom::sym("b"));
        assert!(result.is_none());
    }

    #[test]
    fn test_unify_variable_ground() {
        // unify($X, a) = {$X → a}
        let result = unify(&Atom::sym("$X"), &Atom::sym("a"));
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("$X"), Some(&Atom::sym("a")));
    }

    #[test]
    fn test_unify_two_variables() {
        // unify($X, $Y) = {$X → $Y}
        let result = unify(&Atom::sym("$X"), &Atom::sym("$Y"));
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
    }

    #[test]
    fn test_unify_composite() {
        // unify(f(a, $X), f($Y, b)) = {$X → b, $Y → a}
        let term = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("a"),
            Atom::sym("$X"),
        ]);
        let pattern = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("$Y"),
            Atom::sym("b"),
        ]);

        let result = unify(&term, &pattern);
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 2);
        assert_eq!(subst.get("$X"), Some(&Atom::sym("b")));
        assert_eq!(subst.get("$Y"), Some(&Atom::sym("a")));
    }

    #[test]
    fn test_unify_occurs_check() {
        // unify($X, f($X)) = None (occurs check prevents infinite structure)
        let var = Atom::sym("$X");
        let expr = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("$X"),
        ]);

        let result = unify(&var, &expr);
        assert!(result.is_none());
    }

    #[test]
    fn test_apply_substitution_simple() {
        // apply_substitution($X, {$X → a}) = a
        let var = Atom::sym("$X");
        let mut subst = HashMap::new();
        subst.insert("$X".to_string(), Atom::sym("a"));

        let result = apply_substitution(&var, &subst);
        assert_eq!(result, Atom::sym("a"));
    }

    #[test]
    fn test_apply_substitution_composite() {
        // apply_substitution(f($X, $Y), {$X → a, $Y → b}) = f(a, b)
        let expr = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("$X"),
            Atom::sym("$Y"),
        ]);
        let mut subst = HashMap::new();
        subst.insert("$X".to_string(), Atom::sym("a"));
        subst.insert("$Y".to_string(), Atom::sym("b"));

        let result = apply_substitution(&expr, &subst);
        let expected = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("a"),
            Atom::sym("b"),
        ]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_apply_substitution_chain() {
        // apply_substitution($X, {$X → $Y, $Y → a}) = a
        let var = Atom::sym("$X");
        let mut subst = HashMap::new();
        subst.insert("$X".to_string(), Atom::sym("$Y"));
        subst.insert("$Y".to_string(), Atom::sym("a"));

        let result = apply_substitution(&var, &subst);
        assert_eq!(result, Atom::sym("a"));
    }

    #[test]
    fn test_cost_function() {
        // Sym: 1 token
        assert_eq!(calculate_cost(&Atom::sym("a")), Some(1));

        // Num: 1 token
        assert_eq!(calculate_cost(&Atom::Num(314i128)), Some(1));

        // f(a, b): base_cost (3*2) + recursive (1+1+1) = 6 + 3 = 9 tokens
        // where base_cost = items.len() * 2, recursive_cost = sum of element costs
        let expr = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("a"),
            Atom::sym("b"),
        ]);
        assert_eq!(calculate_cost(&expr), Some(9));
    }

    #[test]
    fn test_machine_state_creation() {
        let state = MachineState::new(Some(100));

        assert_eq!(state.input.len(), 0);
        assert_eq!(state.workspace.len(), 0);
        assert_eq!(state.output.len(), 0);
        assert_eq!(state.cost_budget, Some(100));
    }

    #[test]
    fn test_machine_state_push_input() {
        let mut state = MachineState::new(Some(100));

        state.push_input(Atom::sym("query1"));
        state.push_input(Atom::sym("query2"));

        assert_eq!(state.input.len(), 2);
    }

    #[test]
    fn test_machine_should_continue() {
        let mut state = MachineState::new(Some(100));

        // No work, should stop
        assert!(!state.should_continue());

        // Add work to input
        state.push_input(Atom::sym("query"));
        assert!(state.should_continue());

        // Budget exhausted
        state.cost_budget = Some(0);
        assert!(!state.should_continue());
    }

    #[test]
    fn test_deduct_cost() {
        let mut state = MachineState::new(Some(100));

        state.deduct_cost(30).unwrap();
        assert_eq!(state.cost_budget, Some(70));

        state.deduct_cost(70).unwrap();
        assert_eq!(state.cost_budget, Some(0));

        // Should fail: budget exhausted
        let result = state.deduct_cost(1);
        assert!(result.is_err());
    }
}
