// Phase 1: Machine State Foundation Tests
//
// Reference: Meta-MeTTa specification, Section 3.3
// These tests validate the 4-register state machine implementation.

use mork_metta::atom::Atom;
use mork_metta::eval::{MachineState, unify, apply_substitution, calculate_cost};
use std::collections::HashMap;

#[test]
fn test_phase1_unify_ground_atoms() {
    // unify(a, a) = {} (empty substitution)
    let result = unify(&Atom::sym("a"), &Atom::sym("a"));
    assert!(result.is_some());
    assert_eq!(result.unwrap().len(), 0);
}

#[test]
fn test_phase1_unify_ground_atoms_fail() {
    // unify(a, b) = None (atoms don't match)
    let result = unify(&Atom::sym("a"), &Atom::sym("b"));
    assert!(result.is_none());
}

#[test]
fn test_phase1_unify_variable_ground() {
    // unify($X, a) = {$X → a}
    let result = unify(&Atom::sym("$X"), &Atom::sym("a"));
    assert!(result.is_some());
    let subst = result.unwrap();
    assert_eq!(subst.len(), 1);
    assert_eq!(subst.get("$X"), Some(&Atom::sym("a")));
}

#[test]
fn test_phase1_unify_two_variables() {
    // unify($X, $Y) = {$X → $Y}
    let result = unify(&Atom::sym("$X"), &Atom::sym("$Y"));
    assert!(result.is_some());
    let subst = result.unwrap();
    assert_eq!(subst.len(), 1);
    assert!(subst.contains_key("$X") || subst.contains_key("$Y"));
}

#[test]
fn test_phase1_unify_composite() {
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
fn test_phase1_unify_occurs_check() {
    // unify($X, f($X)) = None (occurs check prevents infinite structure)
    // This is critical for preventing infinite unification chains
    let var = Atom::sym("$X");
    let expr = Atom::Expr(vec![
        Atom::sym("f"),
        Atom::sym("$X"),
    ]);

    let result = unify(&var, &expr);
    assert!(result.is_none(), "Occurs check should prevent $X = f($X)");
}

#[test]
fn test_phase1_apply_substitution_simple() {
    // apply_substitution($X, {$X → a}) = a
    let var = Atom::sym("$X");
    let mut subst = HashMap::new();
    subst.insert("$X".to_string(), Atom::sym("a"));

    let result = apply_substitution(&var, &subst);
    assert_eq!(result, Atom::sym("a"));
}

#[test]
fn test_phase1_apply_substitution_composite() {
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
fn test_phase1_apply_substitution_chain() {
    // apply_substitution($X, {$X → $Y, $Y → a}) = a
    // Tests that substitution chains are followed correctly
    let var = Atom::sym("$X");
    let mut subst = HashMap::new();
    subst.insert("$X".to_string(), Atom::sym("$Y"));
    subst.insert("$Y".to_string(), Atom::sym("a"));

    let result = apply_substitution(&var, &subst);
    assert_eq!(result, Atom::sym("a"));
}

#[test]
fn test_phase1_cost_function_atoms() {
    // Single atoms cost 1 token each
    assert_eq!(calculate_cost(&Atom::sym("a")), Some(1));
    assert_eq!(calculate_cost(&Atom::Num(314i128)), Some(1));
}

#[test]
fn test_phase1_cost_function_composite() {
    // f(a, b): base cost 3*2=6 (3 elements) + recursive 1+1+1=3 = 9 tokens
    let expr = Atom::Expr(vec![
        Atom::sym("f"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]);
    assert_eq!(calculate_cost(&expr), Some(9));
}

#[test]
fn test_phase1_machine_state_creation() {
    // Create initial state with 100 token budget
    let state = MachineState::new(Some(100));

    assert_eq!(state.input.len(), 0);
    assert_eq!(state.workspace.len(), 0);
    assert_eq!(state.output.len(), 0);
    assert_eq!(state.cost_budget, Some(100));
}

#[test]
fn test_phase1_machine_state_unlimited_budget() {
    // Create state with unlimited budget (None)
    let state = MachineState::new(None);
    assert_eq!(state.cost_budget, None);
}

#[test]
fn test_phase1_machine_state_push_input() {
    // Test input register operations
    let mut state = MachineState::new(Some(100));

    state.push_input(Atom::sym("query1"));
    state.push_input(Atom::sym("query2"));

    assert_eq!(state.input.len(), 2);
}

#[test]
fn test_phase1_machine_should_continue() {
    // Test loop control: should_continue()
    let mut state = MachineState::new(Some(100));

    // No work, should not continue
    assert!(!state.should_continue());

    // Add work to input
    state.push_input(Atom::sym("query"));
    assert!(state.should_continue());

    // Budget exhausted
    state.cost_budget = Some(0);
    assert!(!state.should_continue());
}

#[test]
fn test_phase1_machine_deduct_cost() {
    // Test cost accounting
    let mut state = MachineState::new(Some(100));

    state.deduct_cost(30).unwrap();
    assert_eq!(state.cost_budget, Some(70));

    state.deduct_cost(70).unwrap();
    assert_eq!(state.cost_budget, Some(0));

    // Should fail: budget exhausted
    let result = state.deduct_cost(1);
    assert!(result.is_err());
}

#[test]
fn test_phase1_spec_compliance() {
    // Verify: State = ⟨i, k, w, o⟩ (Section 3.3, p. 9)
    // "The 4-register formalization must have four distinct registers"
    let state = MachineState::new(Some(1000));

    // i: input register (Section 3.3, p. 9)
    assert!(state.input.is_empty());

    // w: workspace register (Section 3.3, p. 9)
    assert!(state.workspace.is_empty());

    // o: output register (Section 3.3, p. 9)
    assert!(state.output.is_empty());

    // k: knowledge base (Section 3.3, p. 9) — accessed via FnTable

    // cost_budget: from spec Section 6.3 (p. 15-18)
    assert_eq!(state.cost_budget, Some(1000));
}

#[test]
fn test_phase1_robinson_unification() {
    // Spec Section 3.3: unification must use Robinson's algorithm
    // Test case from standard logic programming literature:
    // unify(f(a, $X, c), f($Y, b, c)) = {$Y → a, $X → b}

    let term = Atom::Expr(vec![
        Atom::sym("f"),
        Atom::sym("a"),
        Atom::sym("$X"),
        Atom::sym("c"),
    ]);
    let pattern = Atom::Expr(vec![
        Atom::sym("f"),
        Atom::sym("$Y"),
        Atom::sym("b"),
        Atom::sym("c"),
    ]);

    let result = unify(&term, &pattern);
    assert!(result.is_some());
    let subst = result.unwrap();
    assert_eq!(subst.len(), 2);
    assert_eq!(subst.get("$X"), Some(&Atom::sym("b")));
    assert_eq!(subst.get("$Y"), Some(&Atom::sym("a")));
}
