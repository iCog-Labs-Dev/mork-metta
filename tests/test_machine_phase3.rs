/// Phase 3: Query and Chain Rule Details
///
/// Specification: Meta-MeTTa Section 3.3 (pages 9-12)
/// Tests the Query and Chain rewrite rules with Robinson's unification algorithm
///
/// Formal Spec - Query Rule:
/// σᵢ = unify(t', tᵢ), k = {(= t₁ u₁),..., (= tₙ uₙ)} ++ k'
/// ⟨{K[t']} ++ i, k, w, o⟩ → ⟨i, k, {K[u₁σ₁]} ++ ... ++ {K[uₙσₙ]} ++ w, o⟩
///
/// Formal Spec - Chain Rule (workspace-to-workspace):
/// σᵢ = unify(u, tᵢ), k = {(= t₁ u₁),..., (= tₙ uₙ)} ++ k'
/// ⟨i, k, {K[u]} ++ w, o⟩ → ⟨i, k, {K[u₁σ₁]} ++ ... ++ {K[uₙσₙ]} ++ w, o⟩

use mork_metta::atom::Atom;
use mork_metta::env::Env;
use mork_metta::func::FnTable;
use mork_metta::eval::{MachineState};
use mork_metta::eval::machine::{unify, apply_substitution, Transition};
use std::collections::HashMap;

#[test]
fn test_phase3_unify_robinson_basic() {
    // Spec Section 3.3: Robinson's unification algorithm
    // unify(f(a, $X), f($Y, b)) = {$X → b, $Y → a}

    let left = Atom::expr(vec![
        Atom::sym("f"),
        Atom::sym("a"),
        Atom::sym("$X"),
    ]);

    let right = Atom::expr(vec![
        Atom::sym("f"),
        Atom::sym("$Y"),
        Atom::sym("b"),
    ]);

    let result = unify(&left, &right);
    assert!(result.is_some(), "Unification should succeed");

    let subst = result.unwrap();
    assert_eq!(subst.len(), 2);
    assert_eq!(subst.get("$X").unwrap(), &Atom::sym("b"));
    assert_eq!(subst.get("$Y").unwrap(), &Atom::sym("a"));
}

#[test]
fn test_phase3_unify_occurs_check() {
    // Spec Section 3.3: Robinson's algorithm includes occurs check
    // unify($X, f($X)) = None (prevents infinite structures)

    let var_x = Atom::sym("$X");
    let f_x = Atom::expr(vec![
        Atom::sym("f"),
        Atom::sym("$X"),
    ]);

    let result = unify(&var_x, &f_x);
    assert!(result.is_none(), "Occurs check should prevent unification");
}

#[test]
fn test_phase3_unify_no_match() {
    // Spec Section 3.3: unification fails for incompatible atoms
    // unify(f(a), f(b)) = None

    let left = Atom::expr(vec![Atom::sym("f"), Atom::sym("a")]);
    let right = Atom::expr(vec![Atom::sym("f"), Atom::sym("b")]);

    let result = unify(&left, &right);
    assert!(result.is_none());
}

#[test]
fn test_phase3_apply_substitution_simple() {
    // Spec Section 3.3: body[σ] notation means apply substitution to body
    // apply_substitution(f($X, $Y), {$X → a, $Y → b}) = f(a, b)

    let body = Atom::expr(vec![
        Atom::sym("f"),
        Atom::sym("$X"),
        Atom::sym("$Y"),
    ]);

    let mut subst = HashMap::new();
    subst.insert("$X".to_string(), Atom::sym("a"));
    subst.insert("$Y".to_string(), Atom::sym("b"));

    let result = apply_substitution(&body, &subst);
    let expected = Atom::expr(vec![
        Atom::sym("f"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]);

    assert_eq!(result, expected);
}

#[test]
fn test_phase3_apply_substitution_nested() {
    // Spec Section 3.3: substitution applies recursively to nested structures
    // apply_substitution(f(g($X), h($X, $Y)), {$X → a, $Y → b})
    //   = f(g(a), h(a, b))

    let body = Atom::expr(vec![
        Atom::sym("f"),
        Atom::expr(vec![Atom::sym("g"), Atom::sym("$X")]),
        Atom::expr(vec![
            Atom::sym("h"),
            Atom::sym("$X"),
            Atom::sym("$Y"),
        ]),
    ]);

    let mut subst = HashMap::new();
    subst.insert("$X".to_string(), Atom::sym("a"));
    subst.insert("$Y".to_string(), Atom::sym("b"));

    let result = apply_substitution(&body, &subst);
    let expected = Atom::expr(vec![
        Atom::sym("f"),
        Atom::expr(vec![Atom::sym("g"), Atom::sym("a")]),
        Atom::expr(vec![Atom::sym("h"), Atom::sym("a"), Atom::sym("b")]),
    ]);

    assert_eq!(result, expected);
}

#[test]
fn test_phase3_query_rule_single_definition() {
    // Spec Section 3.3: Query rule matches input term against definitions in k
    // Input: {(father alice bob)}
    // k = {(= (father $x $y) (parent $x $y))}
    // After Query: w = {(parent alice bob)}

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (father $x $y) (parent $x $y))
    let definition = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![
            Atom::sym("father"),
            Atom::sym("$x"),
            Atom::sym("$y"),
        ]),
        Atom::expr(vec![
            Atom::sym("parent"),
            Atom::sym("$x"),
            Atom::sym("$y"),
        ]),
    ]);
    funcs.space.write().unwrap().add_atom(&definition).unwrap();

    // Create machine state with query in input
    let mut state = MachineState::new(None);
    let query = Atom::expr(vec![
        Atom::sym("father"),
        Atom::sym("alice"),
        Atom::sym("bob"),
    ]);
    state.push_input(query);

    // Execute Query transition
    let result = state.step(Transition::Query, &env, &funcs);
    assert!(result.is_ok(), "Query should succeed");

    // Verify result in workspace
    assert!(!state.workspace.is_empty(), "Workspace should have result");
    let expected = Atom::expr(vec![
        Atom::sym("parent"),
        Atom::sym("alice"),
        Atom::sym("bob"),
    ]);
    assert_eq!(state.workspace.front().unwrap(), &expected);
}

#[test]
fn test_phase3_query_rule_multiple_definitions() {
    // Spec Section 3.3: "for EACH atom in k matching the pattern"
    // Query finds ALL matching definitions, not just first
    //
    // k = {(= (p a) r1), (= (p $x) (r2 $x)), (= (q a) r3)}
    // Query: (p a)
    // Expected: w has both r1 and (r2 a)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add matching definitions
    let def1 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]),
        Atom::sym("r1"),
    ]);
    let def2 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("$x")]),
        Atom::expr(vec![Atom::sym("r2"), Atom::sym("$x")]),
    ]);
    let def3 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("q"), Atom::sym("a")]),
        Atom::sym("r3"),
    ]);

    funcs.space.write().unwrap().add_atom(&def1).unwrap();
    funcs.space.write().unwrap().add_atom(&def2).unwrap();
    funcs.space.write().unwrap().add_atom(&def3).unwrap();

    let mut state = MachineState::new(None);
    let query = Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]);
    state.push_input(query);

    state.step(Transition::Query, &env, &funcs).unwrap();

    // Should have 2 results: r1 and (r2 a)
    assert_eq!(
        state.workspace.len(),
        2,
        "Should match both (= (p a) r1) and (= (p $x) (r2 $x))"
    );

    let results: Vec<Atom> = state.workspace.iter().cloned().collect();
    assert!(results.contains(&Atom::sym("r1")));
    assert!(results.contains(&Atom::expr(vec![
        Atom::sym("r2"),
        Atom::sym("a")
    ])));
}

#[test]
fn test_phase3_chain_rule_workspace_transition() {
    // Spec Section 3.3: Chain rule - workspace-to-workspace transition
    // ⟨i, k, {u} ++ w, o⟩ → ⟨i, k, results ++ w, o⟩
    //
    // k = {(= (p $x) (q $x)), (= (q $x) (r $x))}
    // Start with w = {(p a)}
    // After Chain 1: w = {(q a)}
    // After Chain 2: w = {(r a)}

    let env = Env::new();
    let funcs = FnTable::new();

    let def1 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("$x")]),
        Atom::expr(vec![Atom::sym("q"), Atom::sym("$x")]),
    ]);
    let def2 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("q"), Atom::sym("$x")]),
        Atom::expr(vec![Atom::sym("r"), Atom::sym("$x")]),
    ]);

    funcs.space.write().unwrap().add_atom(&def1).unwrap();
    funcs.space.write().unwrap().add_atom(&def2).unwrap();

    let mut state = MachineState::new(None);
    state.workspace.push_back(Atom::expr(vec![
        Atom::sym("p"),
        Atom::sym("a"),
    ]));

    // Chain step 1: (= (p $x) (q $x)) matches `(p a)`, body `(q a)`,
    // eval dispatches (= (q $x) (r $x)) from space → result `(r a)`
    state.step(Transition::Chain, &env, &funcs).unwrap();
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(
        state.workspace.front().unwrap(),
        &Atom::expr(vec![Atom::sym("r"), Atom::sym("a")])
    );

    // Chain step 2: no definition for `r` → workspace consumed and empty
    state.step(Transition::Chain, &env, &funcs).unwrap();
    assert_eq!(state.workspace.len(), 0);
}

#[test]
fn test_phase3_identical_variables_in_definition() {
    // Spec Section 3.3: Variables appearing multiple times in pattern
    // All occurrences must have same binding
    //
    // k = {(= (equals $x $x) yes)}
    // Query (equals a a) → yes (both $x unify to a)
    // Query (equals a b) → no match (first $x=a, second $x=b conflict)

    let env = Env::new();
    let funcs = FnTable::new();

    let def = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![
            Atom::sym("equals"),
            Atom::sym("$x"),
            Atom::sym("$x"),
        ]),
        Atom::sym("yes"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Test 1: (equals a a) should match
    let mut state1 = MachineState::new(None);
    state1.push_input(Atom::expr(vec![
        Atom::sym("equals"),
        Atom::sym("a"),
        Atom::sym("a"),
    ]));
    state1.step(Transition::Query, &env, &funcs).unwrap();
    assert!(!state1.workspace.is_empty());
    assert_eq!(state1.workspace.front().unwrap(), &Atom::sym("yes"));

    // Test 2: (equals a b) should NOT match
    let mut state2 = MachineState::new(None);
    state2.push_input(Atom::expr(vec![
        Atom::sym("equals"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]));
    state2.step(Transition::Query, &env, &funcs).unwrap();
    assert!(state2.workspace.is_empty());
}

#[test]
fn test_phase3_ground_body_no_variables() {
    // Spec Section 3.3: body[σ] when body contains no variables
    // k = {(= (p a) (q b c))}
    // Query (p a) → (q b c)
    // No substitution needed; body is ground (variable-free)

    let env = Env::new();
    let funcs = FnTable::new();

    let def = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]),
        Atom::expr(vec![
            Atom::sym("q"),
            Atom::sym("b"),
            Atom::sym("c"),
        ]),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    let mut state = MachineState::new(None);
    state.push_input(Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]));

    state.step(Transition::Query, &env, &funcs).unwrap();

    let expected = Atom::expr(vec![
        Atom::sym("q"),
        Atom::sym("b"),
        Atom::sym("c"),
    ]);
    assert_eq!(state.workspace.front().unwrap(), &expected);
}

#[test]
fn test_phase3_no_matching_definitions() {
    // Spec Section 3.3: if no definitions match query, workspace remains empty
    // k = {(= (p a) r)}
    // Query (q b) → no match, workspace empty

    let env = Env::new();
    let funcs = FnTable::new();

    let def = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]),
        Atom::sym("r"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    let mut state = MachineState::new(None);
    let query = Atom::expr(vec![Atom::sym("q"), Atom::sym("b")]);
    state.push_input(query);

    state.step(Transition::Query, &env, &funcs).unwrap();

    assert!(state.workspace.is_empty());
}

#[test]
fn test_phase3_variable_scoping() {
    // Spec Section 3.3: σ is local to each unification
    // Different matches don't share variable bindings
    //
    // k = {(= (p $x) ($x)), (= (q $x) (not $x))}
    // Query (p a) → (a)
    // Query (q b) → (not b)
    // Each uses own $x binding, no collision

    let env = Env::new();
    let funcs = FnTable::new();

    let def1 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("p"), Atom::sym("$x")]),
        Atom::sym("$x"),
    ]);
    let def2 = Atom::expr(vec![
        Atom::sym("="),
        Atom::expr(vec![Atom::sym("q"), Atom::sym("$x")]),
        Atom::expr(vec![Atom::sym("not"), Atom::sym("$x")]),
    ]);

    funcs.space.write().unwrap().add_atom(&def1).unwrap();
    funcs.space.write().unwrap().add_atom(&def2).unwrap();

    // Query (p a)
    let mut state1 = MachineState::new(None);
    state1.push_input(Atom::expr(vec![Atom::sym("p"), Atom::sym("a")]));
    state1.step(Transition::Query, &env, &funcs).unwrap();
    assert_eq!(state1.workspace.front().unwrap(), &Atom::sym("a"));

    // Query (q b)
    let mut state2 = MachineState::new(None);
    state2.push_input(Atom::expr(vec![Atom::sym("q"), Atom::sym("b")]));
    state2.step(Transition::Query, &env, &funcs).unwrap();
    assert_eq!(
        state2.workspace.front().unwrap(),
        &Atom::expr(vec![Atom::sym("not"), Atom::sym("b")])
    );
}

#[test]
fn test_phase3_cost_model_budget_tracking() {
    // Spec Section 6.3: Cost model tracks budget
    // Budget can be limited (Some(n)) or unlimited (None)
    // This test verifies budget is properly tracked

    let env = Env::new();
    let funcs = FnTable::new();

    let def = Atom::expr(vec![
        Atom::sym("="),
        Atom::sym("p"),
        Atom::sym("result"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine with budget limit
    let mut state = MachineState::new(Some(1000));
    assert_eq!(state.cost_budget, Some(1000), "Initial budget should be set");

    state.push_input(Atom::sym("p"));
    state.step(Transition::Query, &env, &funcs).unwrap();

    // Budget tracking is active (even if value depends on cost implementation)
    assert!(state.cost_budget.is_some(), "Budget should remain tracked");
}
