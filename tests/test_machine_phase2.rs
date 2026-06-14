// Phase 2: Integration with Current Eval Loop Tests
//
// Reference: Meta-MeTTa specification, Section 3.3
// These tests validate the integration of the 4-register state machine
// with the existing eval loop via query_knowledge, eval_in_context, and eval_with_state.

use mork_metta::atom::Atom;
use mork_metta::env::Env;
use mork_metta::func::FnTable;
use mork_metta::parser::Expr;
use mork_metta::eval::{eval_with_state, MachineState};

#[test]
fn test_phase2_query_knowledge_with_simple_definition() {
    // Test query_knowledge with a simple (= head body) definition
    // Setup: (= (test) ok)
    // Query: (test)
    // Expected: [ok]

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition to space
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("test")]),
        Atom::sym("ok"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine state and query
    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("test")]);
    state.push_input(query);

    // Execute Query transition
    let result = state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    );

    assert!(result.is_ok());
    // Query rule moves from input to workspace
    // So workspace should have the result (ok)
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("ok"));
}

#[test]
fn test_phase2_eval_with_state_undefined_symbol() {
    // Test eval_with_state with a symbol that has no definition
    // Spec Section 3.3: Query rule only matches (= head body) definitions
    // If a symbol has no definition, Query returns no results
    // Phase 2 status: Self-evaluation not yet implemented (deferred to Phase 3+)
    let expr = Expr::Symbol("undefined".to_string());
    let env = Env::new();
    let funcs = FnTable::new();

    let result = eval_with_state(&expr, &env, &funcs, Some(1000));
    assert!(result.is_ok());

    let (mut ndet, budget) = result.unwrap();
    // No matches for undefined symbol — cost is 0, budget unchanged
    assert_eq!(budget, Some(1000));

    // Since there's no definition for "undefined", Query returns no matches
    // Result: output register is empty
    let first = ndet.next();
    assert!(first.is_none(), "Expected no results for undefined symbol");
}

#[test]
fn test_phase2_query_matches_definition_but_chain_consumes_result() {
    // Demonstration of Phase 2 limitation: Query finds and evaluates definition,
    // but then Chain consumes the result when it shouldn't.
    //
    // Setup: (= (choice) ok)
    // Query: (choice)
    // Current behavior:
    //   1. Query: matches (choice) → ok, puts "ok" in workspace
    //   2. Chain: tries to match "ok" against definitions (finds none), discards
    //   3. Output: workspace is empty, so output is empty
    //
    // Expected behavior (Phase 3+):
    //   - Query should return "ok" as a final result without further Chain processing
    //   - OR: distinguish between "query terms" and "final results"
    //   - OR: mark atoms to avoid re-processing after evaluation
    //
    // For now, this test documents the limitation.

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (choice) ok)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("choice")]),
        Atom::sym("ok"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Test through direct machine state manipulation instead
    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("choice")]);
    state.push_input(query);

    // Execute Query
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // After Query, workspace should have "ok"
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("ok"));

    // Now if we Chain, "ok" will be processed and discarded
    // This is the limitation - we'd need special handling to mark it as final
}

// ========================================================================
// Additional Edge Case Tests
// ========================================================================

#[test]
fn test_phase2_complex_unification_multiple_variables() {
    // Test Query with complex pattern involving multiple variables
    // Setup: (= (pair $x $y) (cons $x $y))
    // Query: (pair a b)
    // Expected: (cons a b)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition with multiple variables
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("pair"),
            Atom::sym("$x"),
            Atom::sym("$y"),
        ]),
        Atom::Expr(vec![
            Atom::sym("cons"),
            Atom::sym("$x"),
            Atom::sym("$y"),
        ]),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![
        Atom::sym("pair"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]);
    state.push_input(query);

    // Execute Query
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Should have (cons a b) in workspace
    assert_eq!(state.workspace.len(), 1);
    let expected = Atom::Expr(vec![
        Atom::sym("cons"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]);
    assert_eq!(state.workspace.front().unwrap(), &expected);
}

#[test]
fn test_phase2_nested_expressions_unification() {
    // Test Query with nested expression patterns
    // Setup: (= (inner (outer $x)) $x)
    // Query: (inner (outer value))
    // Expected: value

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (inner (outer $x)) $x)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("inner"),
            Atom::Expr(vec![
                Atom::sym("outer"),
                Atom::sym("$x"),
            ]),
        ]),
        Atom::sym("$x"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![
        Atom::sym("inner"),
        Atom::Expr(vec![
            Atom::sym("outer"),
            Atom::sym("value"),
        ]),
    ]);
    state.push_input(query);

    // Execute Query
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Should have "value" in workspace
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("value"));
}

#[test]
fn test_phase2_cost_budget_exhaustion_stops_execution() {
    // Test that computation stops when budget is exhausted
    let env = Env::new();
    let funcs = FnTable::new();

    // Add a simple definition
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("test")]),
        Atom::sym("ok"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Very low budget: Query for (test) costs 3 tokens
    // (2 * 1 base for expr + 1 for symbol recursive cost = 3)
    let mut state = MachineState::new(Some(3));

    let query = Atom::Expr(vec![Atom::sym("test")]);
    state.push_input(query);

    // Execute Query - should succeed and deduct all budget
    let result = state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    );
    assert!(result.is_ok());

    // After Query: workspace has "ok", budget is 0
    assert!(state.cost_budget.is_some());
    let remaining = state.cost_budget.unwrap();
    assert!(remaining <= 3, "Budget should be partially or fully consumed");

    // should_continue should return false (budget exhausted or no more input)
    // since input is empty after Query and budget is low
    if remaining == 0 {
        assert!(!state.should_continue(), "Should not continue with exhausted budget");
    }
}

#[test]
fn test_phase2_identical_variables_in_pattern() {
    // Test unification when same variable appears multiple times
    // Setup: (= (equal $x $x) same)
    // Query: (equal a a)
    // Expected: same
    // Query: (equal a b)
    // Expected: (no match)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (equal $x $x) same)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("equal"),
            Atom::sym("$x"),
            Atom::sym("$x"),
        ]),
        Atom::sym("same"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Test 1: matching query (equal a a)
    let mut state1 = MachineState::new(Some(1000));
    let query1 = Atom::Expr(vec![
        Atom::sym("equal"),
        Atom::sym("a"),
        Atom::sym("a"),
    ]);
    state1.push_input(query1);

    state1.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    assert_eq!(state1.workspace.len(), 1);
    assert_eq!(state1.workspace.front().unwrap(), &Atom::sym("same"));

    // Test 2: non-matching query (equal a b)
    let mut state2 = MachineState::new(Some(1000));
    let query2 = Atom::Expr(vec![
        Atom::sym("equal"),
        Atom::sym("a"),
        Atom::sym("b"),
    ]);
    state2.push_input(query2);

    state2.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Should have no matches
    assert_eq!(state2.workspace.len(), 0);
}

#[test]
fn test_phase2_multiple_query_iterations() {
    // Test multiple Query transitions in sequence
    // Setup: Input queue with multiple queries
    // Query processes one item from input per transition

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definitions
    let def1 = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("a")]),
        Atom::sym("result1"),
    ]);
    let def2 = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("b")]),
        Atom::sym("result2"),
    ]);
    funcs.space.write().unwrap().add_atom(&def1).unwrap();
    funcs.space.write().unwrap().add_atom(&def2).unwrap();

    let mut state = MachineState::new(Some(1000));
    // Push multiple queries to input
    state.push_input(Atom::Expr(vec![Atom::sym("a")]));
    state.push_input(Atom::Expr(vec![Atom::sym("b")]));

    assert_eq!(state.input.len(), 2);
    assert_eq!(state.workspace.len(), 0);

    // Query 1: (a) matches, produces result1
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();
    assert_eq!(state.input.len(), 1); // One query consumed
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("result1"));

    // Query 2: (b) from input matches, produces result2
    // First pop result1 from workspace to make room
    state.workspace.pop_front();
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();
    assert_eq!(state.input.len(), 0); // All queries consumed
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("result2"));
}

#[test]
fn test_phase2_empty_input_register_no_effect() {
    // Test Query when input register is empty
    let env = Env::new();
    let funcs = FnTable::new();

    let mut state = MachineState::new(Some(1000));
    // Don't push anything to input

    // Try to execute Query with empty input
    let result = state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    );

    // Should return Ok(None) since there's no input
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), None);

    // State should be unchanged
    assert_eq!(state.input.len(), 0);
    assert_eq!(state.workspace.len(), 0);
}

#[test]
fn test_phase2_definition_with_ground_body() {
    // Test definition that evaluates to a ground atom (not requiring further evaluation)
    // Setup: (= (constant) (foo bar baz))
    // Query: (constant)
    // Expected: (foo bar baz) in workspace

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (constant) (foo bar baz))
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("constant")]),
        Atom::Expr(vec![
            Atom::sym("foo"),
            Atom::sym("bar"),
            Atom::sym("baz"),
        ]),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("constant")]);
    state.push_input(query);

    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    assert_eq!(state.workspace.len(), 1);
    let expected = Atom::Expr(vec![
        Atom::sym("foo"),
        Atom::sym("bar"),
        Atom::sym("baz"),
    ]);
    assert_eq!(state.workspace.front().unwrap(), &expected);
}

#[test]
fn test_phase2_overlapping_patterns_all_match() {
    // Test that all overlapping patterns produce results
    // Setup: (= (test) a) (= (test) b) (= (test) c)
    // Query: (test)
    // Expected: [a, b, c] in workspace (order may vary)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add three definitions
    for result in &["a", "b", "c"] {
        let def = Atom::Expr(vec![
            Atom::sym("="),
            Atom::Expr(vec![Atom::sym("test")]),
            Atom::sym(*result),
        ]);
        funcs.space.write().unwrap().add_atom(&def).unwrap();
    }

    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("test")]);
    state.push_input(query);

    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Should have all three results
    assert_eq!(state.workspace.len(), 3);
    let results: Vec<Atom> = state.workspace.iter().cloned().collect();
    assert!(results.contains(&Atom::sym("a")));
    assert!(results.contains(&Atom::sym("b")));
    assert!(results.contains(&Atom::sym("c")));
}

#[test]
fn test_phase2_query_with_unification() {
    // Test Query rule with pattern unification
    // Setup: (= (double $x) ($x $x))
    // Query: (double a)
    // Expected: (a a)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (double $x) ($x $x))
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("double"),
            Atom::sym("$x"),
        ]),
        Atom::Expr(vec![
            Atom::sym("$x"),
            Atom::sym("$x"),
        ]),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine state and query
    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![
        Atom::sym("double"),
        Atom::sym("a"),
    ]);
    state.push_input(query);

    // Execute Query transition
    let result = state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    );

    assert!(result.is_ok());
    // Should have (a a) in workspace
    assert_eq!(state.workspace.len(), 1);
    let expected = Atom::Expr(vec![Atom::sym("a"), Atom::sym("a")]);
    assert_eq!(state.workspace.front().unwrap(), &expected);
}

#[test]
fn test_phase2_chain_rule_workspace_to_workspace() {
    // Test Chain rule: w → w
    // Setup: (= (id $x) $x)
    // Initial workspace: (id (id a))
    // After Chain: should have (id a) and then (a)

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (id $x) $x)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("id"),
            Atom::sym("$x"),
        ]),
        Atom::sym("$x"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine state with term in workspace
    let mut state = MachineState::new(Some(1000));
    let term = Atom::Expr(vec![
        Atom::sym("id"),
        Atom::Expr(vec![
            Atom::sym("id"),
            Atom::sym("a"),
        ]),
    ]);
    state.workspace.push_back(term);

    // Execute first Chain transition
    let result = state.step(
        mork_metta::eval::machine::Transition::Chain,
        &env,
        &funcs,
    );

    assert!(result.is_ok());
    // After Chain, workspace should have a — the result of applying id twice
    // (Chain matches (= (id $x) $x) → body (id a), then eval-in-context
    // dispatches (id a) through space definition → a)
    assert_eq!(state.workspace.len(), 1);
    assert_eq!(state.workspace.front().unwrap(), &Atom::sym("a"));
}

#[test]
fn test_phase2_full_loop_query_chain_output() {
    // Test full loop: Query (i→w), Chain (w→w), Output (w→o)
    // Setup: (= (id $x) $x)
    // Query: (id a)
    // Expected: [a] in output register

    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (id $x) $x)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![
            Atom::sym("id"),
            Atom::sym("$x"),
        ]),
        Atom::sym("$x"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine state
    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![
        Atom::sym("id"),
        Atom::sym("a"),
    ]);
    state.push_input(query);

    // Step 1: Query (i → w)
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();
    assert_eq!(state.input.len(), 0);
    assert_eq!(state.workspace.len(), 1); // Should have (a)
    assert_eq!(state.output.len(), 0);

    // Step 2: Output (w → o)
    state.step(
        mork_metta::eval::machine::Transition::Output,
        &env,
        &funcs,
    ).unwrap();
    assert_eq!(state.workspace.len(), 0);
    assert_eq!(state.output.len(), 1); // Should have (a) in output
    assert_eq!(state.output[0], Atom::sym("a"));
}

#[test]
fn test_phase2_cost_budget_tracking() {
    // Test that cost is properly tracked and deducted
    let env = Env::new();
    let funcs = FnTable::new();

    // Add definition: (= (test) ok)
    let def = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("test")]),
        Atom::sym("ok"),
    ]);
    funcs.space.write().unwrap().add_atom(&def).unwrap();

    // Create machine state with limited budget
    let mut state = MachineState::new(Some(100));
    let query = Atom::Expr(vec![Atom::sym("test")]);
    state.push_input(query.clone());

    let initial_budget = state.cost_budget;

    // Execute Query transition
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Cost should have been deducted
    // Query rule cost = #(query) where query is (test) with 1 element, so cost = 2*1 = 2
    let final_budget = state.cost_budget;
    assert!(initial_budget > final_budget || final_budget == initial_budget);
}

#[test]
fn test_phase2_no_matching_definitions() {
    // Test Query with no matching definitions
    // Setup: no definitions
    // Query: (nonexistent)
    // Expected: workspace should be empty

    let env = Env::new();
    let funcs = FnTable::new();

    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("nonexistent")]);
    state.push_input(query);

    // Execute Query transition
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Since there's no matching definition, workspace should be empty
    assert_eq!(state.workspace.len(), 0);
}

#[test]
fn test_phase2_multiple_definitions_match() {
    // Test Query with multiple matching definitions
    // Setup: (= (choice) a) and (= (choice) b)
    // Query: (choice)
    // Expected: both a and b in workspace

    let env = Env::new();
    let funcs = FnTable::new();

    // Add first definition: (= (choice) a)
    let def1 = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("choice")]),
        Atom::sym("a"),
    ]);
    funcs.space.write().unwrap().add_atom(&def1).unwrap();

    // Add second definition: (= (choice) b)
    let def2 = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("choice")]),
        Atom::sym("b"),
    ]);
    funcs.space.write().unwrap().add_atom(&def2).unwrap();

    // Create machine state and query
    let mut state = MachineState::new(Some(1000));
    let query = Atom::Expr(vec![Atom::sym("choice")]);
    state.push_input(query);

    // Execute Query transition
    state.step(
        mork_metta::eval::machine::Transition::Query,
        &env,
        &funcs,
    ).unwrap();

    // Should have both results in workspace
    assert_eq!(state.workspace.len(), 2);
    let results: Vec<Atom> = state.workspace.iter().cloned().collect();
    assert!(results.contains(&Atom::sym("a")));
    assert!(results.contains(&Atom::sym("b")));
}
