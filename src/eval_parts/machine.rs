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
use std::collections::{VecDeque, HashMap};
use super::core::eval_in_context;

// ========================================================================
// State Machine: The 4-Register Formalization
// ========================================================================

/// The 4-register operational state machine from Meta-MeTTa spec (Section 3.3)
///
/// Represents computation as transitions between states:
///   ⟨i, k, w, o⟩ → ⟨i', k', w', o'⟩
///
/// - **i**: input register (queries issued, awaiting processing)
/// - **k**: knowledge base (all atoms, including (= head body) definitions)
/// - **w**: workspace (intermediate results from Query/Chain matching)
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
    /// - Ok(None): transition succeeded, no cost (e.g., Output rule)
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
            Transition::Output => self.apply_output(),
        }
    }

    /// Query rule: match term in i against (= ...) in k → put results in w
    ///
    /// Spec Section 3.3, pages 9-10:
    /// ```
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
    pub fn apply_query(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        let term = match self.input.pop_front() {
            Some(t) => t,
            None => return Ok(None),
        };

        let (results, subst_cost, result_cost) = self.query_knowledge_with_cost(&term, env, funcs)?;

        for r in results {
            self.workspace.push_back(r);
        }

        // Cost per spec Section 6.3: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
        let total_cost = subst_cost + result_cost;
        if total_cost > 0 {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= total_cost;
            }
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// Chain rule: match term in w against (= ...) in k → put results in w
    ///
    /// Spec Section 3.3, pages 9-10:
    /// Same as Query, but source/sink both w:
    /// ```
    /// k = {t1, ..., tn} ++ k'
    /// σ = unify(w_term, (= head body))
    /// ⟨i, k, {term} ++ w, o⟩ → ⟨i, k, w ++ {body[σ]}, o⟩
    /// ```
    ///
    /// Matches workspace term against all (= head body) definitions in knowledge base.
    /// Same as Query, except source/sink both come from workspace.
    pub fn apply_chain(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        let term = match self.workspace.pop_front() {
            Some(t) => t,
            None => return Ok(None),
        };

        let (results, subst_cost, result_cost) = self.query_knowledge_with_cost(&term, env, funcs)?;

        for r in results {
            self.workspace.push_back(r);
        }

        // Cost per spec Section 6.3: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
        let total_cost = subst_cost + result_cost;
        if total_cost > 0 {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= total_cost;
            }
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// Helper: query_knowledge_with_cost(term)
    ///
    /// Core unification-and-evaluation loop for Query and Chain rules.
    /// Spec Section 3.3 (pages 9-10), Section 6.3 (cost model).
    ///
    /// Returns (results, substitution_cost, result_cost) where:
    /// - results: Vec<Atom> of all matching results
    /// - substitution_cost: Σᵢ#(σᵢ) sum of unification costs
    /// - result_cost: Σᵢ#(uᵢσᵢ) sum of result costs
    ///
    /// Total cost per spec: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
    fn query_knowledge_with_cost(
        &self,
        term: &Atom,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<(Vec<Atom>, i64, i64), String> {
        let mut results = Vec::new();
        let mut total_subst_cost: i64 = 0;
        let mut total_result_cost: i64 = 0;

        let atoms_snapshot: Vec<Atom> = {
            let space = funcs.space.lock().unwrap();
            space.get_atoms()
        };

        for atom in atoms_snapshot {
            if let Atom::Expr(items) = &atom {
                if items.len() == 3 && items[0] == Atom::sym("=") {
                    let head = &items[1];
                    let body = &items[2];

                    if let Some(substitution) = unify(term, head) {
                        let instantiated_body = apply_substitution(body, &substitution);

                        match eval_in_context(&instantiated_body, env, funcs) {
                            Ok(body_results) => {
                                // Add substitution cost: #(σᵢ)
                                total_subst_cost += Self::cost_substitution(&substitution);

                                // Add result costs: #(uᵢσᵢ)
                                total_result_cost += Self::cost_results(&body_results);

                                results.extend(body_results);
                            }
                            Err(_) => {
                                // Evaluation failed; skip this definition
                            }
                        }
                    }
                }
            }
        }

        Ok((results, total_subst_cost, total_result_cost))
    }

    /// Helper: query_knowledge(term) - backward-compat wrapper
    fn query_knowledge(
        &self,
        term: &Atom,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<Vec<Atom>, String> {
        let (results, _, _) = self.query_knowledge_with_cost(term, env, funcs)?;
        Ok(results)
    }

    /// Transform rule: rewrite atoms in k matching pattern
    ///
    /// This is the meta-rule that enables code evolution.
    /// Spec Section 3.3, pages 10-11:
    /// ```
    /// k = {t1, ..., tn} ++ k'
    /// σi = unify(pattern, ti)  ← for EACH atom in k
    /// ⟨{(transform pattern replacement)} ++ i, k, w, o⟩
    ///   → ⟨i, k, {K1[replacementσ1]...Kn[replacementσn]} ++ w, o⟩
    /// ```
    ///
    /// Extracts (transform pattern replacement) from input register
    /// and rewrites all matching atoms in knowledge base.
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
            let space = funcs.space.lock().unwrap();
            space.get_atoms()
        };

        // Collect all replacements before modifying knowledge base (atomic update)
        let mut replacements: Vec<(Atom, Atom)> = Vec::new();
        let mut transformed_atoms: Vec<Atom> = Vec::new();
        let mut total_subst_cost: i64 = 0;
        let mut total_result_cost: i64 = 0;

        // For each atom in k, try to match pattern
        // Spec Section 3.3: σi = unify(pattern, ti) for EACH atom ti
        for atom in &atoms_snapshot {
            if let Some(subst) = unify(atom, &pattern) {
                // Cost of this unification: #(σᵢ)
                total_subst_cost += Self::cost_substitution(&subst);

                // Compute replacement[σ] - substitution application per spec notation
                let new_atom = apply_substitution(&replacement, &subst);

                // Cost of constructed result: #(uᵢσᵢ)
                if let Some(c) = calculate_cost(&new_atom) {
                    total_result_cost += c;
                }

                replacements.push((atom.clone(), new_atom.clone()));
                transformed_atoms.push(new_atom);
            }
        }

        // Apply all replacements atomically to knowledge base
        if !replacements.is_empty() {
            let mut space = funcs.space.lock().unwrap();

            for (old_atom, new_atom) in replacements {
                space.remove_atom(&old_atom)?;
                space.add_atom(&new_atom)?;

                if let Atom::Expr(items) = &new_atom {
                    if items.len() == 3 && items[0] == Atom::sym("=") {
                        let head = &items[1];
                        let body = &items[2];
                        register_function_definition(head, body, funcs)?;
                    }
                }
            }
        }

        for atom in transformed_atoms {
            self.workspace.push_back(atom);
        }

        // Cost per spec Section 6.3: c = Σᵢ#(σᵢ) + Σᵢ#(uᵢσᵢ)
        let total_cost = total_subst_cost + total_result_cost;
        if total_cost > 0 {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= total_cost;
            }
        }
        Ok(if total_cost > 0 { Some(total_cost) } else { None })
    }

    /// AddAtom rule: add atom to k
    /// Spec Section 3.3, page 11; Section 6.3 cost model
    /// Cost: c = #(atom) per spec (AddAtom1 rule shows #(t))
    pub fn apply_add_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        funcs.space.lock().unwrap().add_atom(&atom)?;
        let cost = calculate_cost(&atom);
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= c;
            }
        }
        Ok(cost)
    }

    /// RemAtom rule: remove atom from k
    /// Spec Section 3.3, page 11; Section 6.3 cost model
    /// Cost: c = #(atom) per spec (RemAtom1 rule shows #(t))
    pub fn apply_remove_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        funcs.space.lock().unwrap().remove_atom(&atom)?;
        let cost = calculate_cost(&atom);
        if let Some(c) = cost {
            if let Some(budget) = self.cost_budget.as_mut() {
                *budget -= c;
            }
        }
        Ok(cost)
    }

    /// Output rule: move result from w to o
    /// Spec Section 3.3, page 12; Section 6.3 cost model
    /// Cost: c = #(u) where u is the term being output (per OUTPUT rule spec)
    pub fn apply_output(&mut self) -> Result<Option<i64>, String> {
        if let Some(term) = self.workspace.pop_front() {
            let cost = calculate_cost(&term);
            self.output.push(term);
            if let Some(c) = cost {
                if let Some(budget) = self.cost_budget.as_mut() {
                    *budget -= c;
                }
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
/// Follows variable bindings through the substitution map.
/// Example: if σ = {$X → $Y, $Y → a}, then deref($X, σ) = a
fn deref(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
    match atom {
        Atom::Sym(v) if v.starts_with('$') => {
            if let Some(target) = subst.get(v.as_ref()) {
                deref(target, subst)  // Follow chain
            } else {
                atom.clone()
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

/// Apply substitution to an atom
///
/// Spec Section 3.3: body[σ] means apply substitution σ to body
/// Recursively substitute all variable occurrences with their bindings.
///
/// Example: apply_substitution(f($X, $Y), {$X → a, $Y → b}) = f(a, b)
pub fn apply_substitution(atom: &Atom, subst: &HashMap<String, Atom>) -> Atom {
    match atom {
        Atom::Sym(v) if v.starts_with('$') => {
            if let Some(target) = subst.get(v.as_ref()) {
                apply_substitution(target, subst)  // Follow chain
            } else {
                atom.clone()
            }
        }
        Atom::Expr(items) => {
            let new_items = items.iter()
                .map(|item| apply_substitution(item, subst))
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
/// ```
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

/// Size-based cost variant (Phase 5)
/// Cost proportional to serialized representation length
pub fn calculate_cost_size(atom: &Atom) -> Option<i64> {
    let s = atom.to_sexpr_string();
    Some(((s.len() as i64) + 9) / 10)
}

/// Complexity-variant cost (Phase 5)
/// Penalizes deeply nested structures
pub fn calculate_cost_complexity(atom: &Atom) -> Option<i64> {
    fn cost_depth(a: &Atom, depth: i64) -> i64 {
        match a {
            Atom::Sym(_) | Atom::Num(_) | Atom::Closure(_) => 1,
            Atom::Expr(items) => {
                let base = 1 + depth;
                let child_costs: i64 = items.iter()
                    .map(|item| cost_depth(item, depth + 1))
                    .sum();
                base + child_costs
            }
        }
    }
    Some(cost_depth(atom, 0))
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

        // f(a, b): 2*2 + 1 + 1 = 6 tokens
        let expr = Atom::Expr(vec![
            Atom::sym("f"),
            Atom::sym("a"),
            Atom::sym("b"),
        ]);
        assert_eq!(calculate_cost(&expr), Some(6));
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
