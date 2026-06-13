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

    // Note: Knowledge base (k) is accessed via FnTable.space in the step() method
    // We don't store it in MachineState to avoid Arc<RwLock<>> lifetime issues
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
        }
    }

    /// Push a term into the input register (new query)
    pub fn push_input(&mut self, atom: Atom) {
        self.input.push_back(atom);
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
    fn apply_query(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        // Pick a term from input register
        let term = match self.input.pop_front() {
            Some(t) => t,
            None => return Ok(None),  // No more input
        };

        // Query knowledge base: find all matching definitions
        let results = self.query_knowledge(&term, env, funcs)?;

        // Add all results to workspace
        for r in results {
            self.workspace.push_back(r);
        }

        // Cost = #(term) where # is polymorphic cost function
        let cost = calculate_cost(&term);
        Ok(cost)
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
    fn apply_chain(&mut self, env: &Env, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        // Pick a term from workspace
        let term = match self.workspace.pop_front() {
            Some(t) => t,
            None => return Ok(None),  // No more work
        };

        // Query knowledge base: find all matching definitions
        let results = self.query_knowledge(&term, env, funcs)?;

        // Add all results back to workspace
        for r in results {
            self.workspace.push_back(r);
        }

        let cost = calculate_cost(&term);
        Ok(cost)
    }

    /// Helper: query_knowledge(term)
    ///
    /// Core unification-and-evaluation loop for Query and Chain rules.
    /// Spec Section 3.3 (pages 9-10).
    ///
    /// Algorithm:
    /// 1. FOR EACH atom in k (knowledge base):
    ///    a. Check if atom matches pattern (= head body)
    ///    b. Unify term with head using Robinson's algorithm → substitution σ
    ///    c. Apply σ to body → instantiated_body (body[σ] in spec notation)
    ///    d. Evaluate instantiated_body → results
    ///    e. Add all results to output vector
    ///
    /// Semantics:
    /// - Unification: σ = unify(term, head) using Robinson's algorithm
    /// - Substitution: apply σ to all variables in body (notation body[σ])
    /// - Evaluation: recursively evaluate the instantiated body
    /// - All matches: finds ALL atoms in k matching pattern, not just first
    /// - Variable scoping: σ is local to each unification; different unifications
    ///   don't share variable bindings
    ///
    /// Returns vector of all results from all matching definitions.
    fn query_knowledge(
        &self,
        term: &Atom,
        env: &Env,
        funcs: &crate::func::FnTable,
    ) -> Result<Vec<Atom>, String> {
        let mut results = Vec::new();

        // Spec Section 3.3: k = {t1, ..., tn} ++ k'
        // Get snapshot of all atoms in k (snapshot to avoid lock issues during iteration)
        let atoms_snapshot: Vec<Atom> = {
            let space = funcs.space.lock().unwrap();
            space.get_atoms()
        };

        // Spec Section 3.3: for EACH atom in k matching the pattern
        for atom in atoms_snapshot {
            // Look for (= head body) definitions in k
            if let Atom::Expr(items) = &atom {
                if items.len() == 3 && items[0] == Atom::sym("=") {
                    let head = &items[1];
                    let body = &items[2];

                    // Spec Section 3.3: σ = unify(term, (= head body))
                    // Robinson's algorithm with occurs check
                    if let Some(substitution) = unify(term, head) {
                        // Spec Section 3.3: body[σ] (apply substitution to body)
                        let instantiated_body = apply_substitution(body, &substitution);

                        // Spec Section 3.3: evaluate body[σ] → get results
                        // This calls back to the main eval loop to get results
                        match eval_in_context(&instantiated_body, env, funcs) {
                            Ok(body_results) => {
                                // All results from evaluating this instantiated body
                                // are added to the output
                                results.extend(body_results);
                            }
                            Err(_) => {
                                // If evaluation fails, this definition doesn't contribute results
                                // Continue to next definition in k
                            }
                        }
                    }
                    // If unification fails, continue to next atom in k
                }
            }
        }

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

        // Parse (transform pattern replacement) structure
        let (pattern, replacement) = match &term {
            Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("transform") => {
                (items[1].clone(), items[2].clone())
            }
            _ => {
                // Invalid transform term; skip
                return Ok(None);
            }
        };

        // Get snapshot of all atoms in k
        let atoms_snapshot: Vec<Atom> = {
            let space = funcs.space.lock().unwrap();
            space.get_atoms()
        };

        let mut replacements = Vec::new();
        let mut transformed_atoms = Vec::new();

        // For each atom in k, try to match pattern
        for atom in &atoms_snapshot {
            if let Some(subst) = unify(atom, &pattern) {
                // Compute replacement[σ]
                let new_atom = apply_substitution(&replacement, &subst);
                replacements.push((atom.clone(), new_atom.clone()));
                transformed_atoms.push(new_atom);
            }
        }

        // Apply replacements to knowledge base
        if !replacements.is_empty() {
            let mut space = funcs.space.lock().unwrap();
            for (old_atom, new_atom) in replacements {
                space.remove_atom(&old_atom)?;
                space.add_atom(&new_atom)?;

                // If new atom is a function definition (= head body), register it
                // Function registration deferred to integration phase
                if let Atom::Expr(items) = &new_atom {
                    if items.len() == 3 && items[0] == Atom::sym("=") {
                        // This is code evolution: transformed atom is a function definition
                        // Future: register with funcs for callable lookup
                    }
                }
            }
        }

        // Add all transformed atoms to workspace
        for atom in transformed_atoms {
            self.workspace.push_back(atom);
        }

        let cost = calculate_cost(&pattern);
        Ok(cost)
    }

    /// AddAtom rule: add atom to k
    /// Spec Section 3.3, page 11
    fn apply_add_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        funcs.space.lock().unwrap().add_atom(&atom)?;
        Ok(Some(10))  // AddAtom has fixed cost
    }

    /// RemAtom rule: remove atom from k
    /// Spec Section 3.3, page 11
    fn apply_remove_atom(&mut self, atom: Atom, funcs: &crate::func::FnTable) -> Result<Option<i64>, String> {
        funcs.space.lock().unwrap().remove_atom(&atom)?;
        Ok(Some(10))  // RemAtom has fixed cost
    }

    /// Output rule: move result from w to o
    /// Spec Section 3.3, page 12
    fn apply_output(&mut self) -> Result<Option<i64>, String> {
        // Move one result from workspace to output
        if let Some(term) = self.workspace.pop_front() {
            self.output.push(term);
        }
        Ok(None)  // Output rule has no cost
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
