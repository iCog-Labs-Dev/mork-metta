use mork_metta::atom::Atom;
use mork_metta::env::Env;
use mork_metta::eval_parts::machine::{MachineState, unify, apply_substitution};
use mork_metta::func::FnTable;

fn setup() -> (MachineState, Env, FnTable) {
    (MachineState::new(Some(10000)), Env::new(), FnTable::new())
}

#[test]
fn test_transform_basic_atoms() {
    let (mut state, env, funcs) = setup();

    // Add atoms to knowledge base
    funcs.space.write().unwrap().add_atom(&Atom::sym("slow")).unwrap();
    funcs.space.write().unwrap().add_atom(&Atom::sym("slow")).unwrap();

    // Create transform term: (transform slow fast)
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::sym("slow"),
        Atom::sym("fast"),
    ]);

    state.push_input(transform_term);

    // Execute Transform
    let result = state.apply_transform(&env, &funcs);
    assert!(result.is_ok(), "Transform should succeed");
    assert!(!state.workspace.is_empty(), "Workspace should have transformed atoms");
    assert!(
        state.workspace.iter().any(|a| a == &Atom::sym("fast")),
        "Workspace should have 'fast'"
    );
}

#[test]
fn test_transform_with_variables() {
    let (mut state, env, funcs) = setup();

    // Add atoms: (slow-fib 5), (slow-fib 10)
    let space = funcs.space.write().unwrap();
    space.add_atom(&Atom::expr(vec![Atom::sym("slow-fib"), Atom::num(5)])).unwrap();
    space.add_atom(&Atom::expr(vec![Atom::sym("slow-fib"), Atom::num(10)])).unwrap();
    drop(space);

    // Transform (slow-fib $n) to (fast-fib $n)
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![Atom::sym("slow-fib"), Atom::sym("$n")]),
        Atom::expr(vec![Atom::sym("fast-fib"), Atom::sym("$n")]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    // Should have 2 transformed atoms in workspace
    assert_eq!(state.workspace.len(), 2, "Should have 2 transformed atoms");

    // Verify both (fast-fib 5) and (fast-fib 10) are present
    let expected1 = Atom::expr(vec![Atom::sym("fast-fib"), Atom::num(5)]);
    let expected2 = Atom::expr(vec![Atom::sym("fast-fib"), Atom::num(10)]);

    let mut ws_atoms = Vec::new();
    while let Some(atom) = state.workspace.pop_front() {
        ws_atoms.push(atom);
    }

    assert!(ws_atoms.contains(&expected1), "Workspace should contain (fast-fib 5)");
    assert!(ws_atoms.contains(&expected2), "Workspace should contain (fast-fib 10)");
}

#[test]
fn test_transform_all_matches() {
    let (mut state, env, funcs) = setup();

    // Add multiple matching atoms
    {
        let space = funcs.space.write().unwrap();
        for i in 1..=5 {
            space.add_atom(&Atom::expr(vec![
                Atom::sym("test"),
                Atom::num(i as i128),
            ])).unwrap();
        }
    }

    // Transform all (test $x) to (done $x)
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![Atom::sym("test"), Atom::sym("$x")]),
        Atom::expr(vec![Atom::sym("done"), Atom::sym("$x")]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    // Should have 5 transformed atoms
    assert_eq!(state.workspace.len(), 5, "Should transform all 5 matching atoms");

    // Verify all have correct form
    while let Some(atom) = state.workspace.pop_front() {
        if let Atom::Expr(items) = &atom {
            assert_eq!(items[0], Atom::sym("done"));
            assert!(matches!(items[1], Atom::Num(_)));
        }
    }
}

#[test]
fn test_transform_no_matches() {
    let (mut state, env, funcs) = setup();

    // Add atoms that won't match
    funcs.space.write().unwrap().add_atom(&Atom::sym("foo")).unwrap();
    funcs.space.write().unwrap().add_atom(&Atom::sym("bar")).unwrap();

    // Try to transform non-existent pattern
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::sym("baz"),
        Atom::sym("qux"),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    assert!(state.workspace.is_empty(), "Workspace should be empty when no atoms match");
}

#[test]
fn test_transform_nested_patterns() {
    let (mut state, env, funcs) = setup();

    // Add nested structures
    {
        let space = funcs.space.write().unwrap();
        space.add_atom(&Atom::expr(vec![
            Atom::sym("pair"),
            Atom::sym("a"),
            Atom::sym("b"),
        ])).unwrap();
        space.add_atom(&Atom::expr(vec![
            Atom::sym("pair"),
            Atom::sym("x"),
            Atom::sym("y"),
        ])).unwrap();
    }

    // Transform (pair $a $b) to (tuple $b $a) - swap arguments
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![
            Atom::sym("pair"),
            Atom::sym("$a"),
            Atom::sym("$b"),
        ]),
        Atom::expr(vec![
            Atom::sym("tuple"),
            Atom::sym("$b"),
            Atom::sym("$a"),
        ]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    assert_eq!(state.workspace.len(), 2, "Should have 2 transformed atoms");

    // Verify arguments are swapped
    let mut tuples = Vec::new();
    while let Some(atom) = state.workspace.pop_front() {
        if let Atom::Expr(items) = atom {
            if items.len() == 3 && items[0] == Atom::sym("tuple") {
                tuples.push((items[1].clone(), items[2].clone()));
            }
        }
    }

    assert_eq!(tuples.len(), 2, "Should have 2 tuples");
    // Verify we have (tuple b a) and (tuple y x) - arguments are swapped
    assert!(tuples.contains(&(Atom::sym("b"), Atom::sym("a"))), "Should have (tuple b a)");
    assert!(tuples.contains(&(Atom::sym("y"), Atom::sym("x"))), "Should have (tuple y x)");
}

#[test]
fn test_transform_removes_old_atoms() {
    let (mut state, env, funcs) = setup();

    // Add atoms
    funcs.space.write().unwrap().add_atom(&Atom::sym("old")).unwrap();

    // Transform old to new
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::sym("old"),
        Atom::sym("new"),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    // Per spec, Transform puts results in workspace, doesn't mutate k
    // Old atom should still be in k (Transform doesn't remove from k)
    let atoms = funcs.space.read().unwrap().get_atoms();
    assert!(atoms.contains(&Atom::sym("old")), "Old atom should remain in k");
    assert!(
        state.workspace.iter().any(|a| a == &Atom::sym("new")),
        "Workspace should have 'new'"
    );
}

#[test]
fn test_transform_with_multiple_variables() {
    let (mut state, env, funcs) = setup();

    // Add atoms with multiple variables
    funcs.space.write().unwrap().add_atom(&Atom::expr(vec![
        Atom::sym("rel"),
        Atom::sym("alice"),
        Atom::sym("bob"),
        Atom::sym("charlie"),
    ])).unwrap();

    // Transform (rel $x $y $z) to (triple $z $y $x) - reverse order
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![
            Atom::sym("rel"),
            Atom::sym("$x"),
            Atom::sym("$y"),
            Atom::sym("$z"),
        ]),
        Atom::expr(vec![
            Atom::sym("triple"),
            Atom::sym("$z"),
            Atom::sym("$y"),
            Atom::sym("$x"),
        ]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    assert_eq!(state.workspace.len(), 1);

    let transformed = state.workspace.pop_front().unwrap();
    if let Atom::Expr(items) = transformed {
        assert_eq!(items[0], Atom::sym("triple"));
        assert_eq!(items[1], Atom::sym("charlie")); // $z
        assert_eq!(items[2], Atom::sym("bob"));     // $y
        assert_eq!(items[3], Atom::sym("alice"));   // $x
    }
}

#[test]
fn test_transform_empty_input() {
    let (mut state, env, funcs) = setup();

    // Try to transform with empty input
    let result = state.apply_transform(&env, &funcs);
    assert!(result.is_ok());
    assert!(state.workspace.is_empty());
}

#[test]
fn test_transform_invalid_format_missing_replacement() {
    let (mut state, env, funcs) = setup();

    // Push malformed transform: missing replacement argument
    state.push_input(Atom::expr(vec![
        Atom::sym("transform"),
        Atom::sym("only-one-arg"),
    ]));

    let result = state.apply_transform(&env, &funcs);
    // Should error on malformed input
    assert!(result.is_err(), "Should error on malformed transform");
}

#[test]
fn test_transform_invalid_format_no_args() {
    let (mut state, env, funcs) = setup();

    // Push malformed transform: no arguments
    state.push_input(Atom::expr(vec![
        Atom::sym("transform"),
    ]));

    let result = state.apply_transform(&env, &funcs);
    // Should error on malformed input
    assert!(result.is_err(), "Should error on malformed transform");
}

#[test]
fn test_transform_not_builtin() {
    let (mut state, env, funcs) = setup();

    // Push something that looks like transform but isn't the builtin
    state.push_input(Atom::expr(vec![
        Atom::sym("my-transform"),
        Atom::sym("pattern"),
        Atom::sym("replacement"),
    ]));

    let result = state.apply_transform(&env, &funcs);
    assert!(result.is_ok());
    assert!(state.workspace.is_empty(), "Non-builtin should be silently skipped");
}

#[test]
fn test_transform_preserves_non_matching_atoms() {
    let (mut state, env, funcs) = setup();

    // Add mixed atoms
    {
        let space = funcs.space.write().unwrap();
        space.add_atom(&Atom::sym("keep1")).unwrap();
        space.add_atom(&Atom::sym("keep2")).unwrap();
        space.add_atom(&Atom::expr(vec![
            Atom::sym("transform-me"),
            Atom::num(1),
        ])).unwrap();
    }

    // Transform only specific pattern
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![
            Atom::sym("transform-me"),
            Atom::sym("$x"),
        ]),
        Atom::expr(vec![
            Atom::sym("transformed"),
            Atom::sym("$x"),
        ]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    // Per spec Transform puts results in workspace, doesn't mutate k
    // Original atoms remain in k
    let atoms = funcs.space.read().unwrap().get_atoms();
    assert!(atoms.contains(&Atom::sym("keep1")));
    assert!(atoms.contains(&Atom::sym("keep2")));
    assert!(
        state.workspace.iter().any(|a| {
            if let Atom::Expr(items) = a {
                items.len() == 2 && items[0] == Atom::sym("transformed")
            } else {
                false
            }
        }),
        "Workspace should have transformed atoms"
    );

}

#[test]
fn test_transform_spec_semantics() {
    let (mut state, env, funcs) = setup();

    // Add atoms: (num 1), (num 2), (num 3)
    {
        let space = funcs.space.write().unwrap();
        for i in 1..=3 {
            space.add_atom(&Atom::expr(vec![
                Atom::sym("num"),
                Atom::num(i as i128),
            ])).unwrap();
        }
    }

    // Transform (num $x) to (even $x)
    let transform_term = Atom::expr(vec![
        Atom::sym("transform"),
        Atom::expr(vec![
            Atom::sym("num"),
            Atom::sym("$x"),
        ]),
        Atom::expr(vec![
            Atom::sym("even"),
            Atom::sym("$x"),
        ]),
    ]);

    state.push_input(transform_term);
    state.apply_transform(&env, &funcs).unwrap();

    // Should have 3 transformed atoms
    assert_eq!(state.workspace.len(), 3);

    // Verify (even 1), (even 2), (even 3) are present
    let mut transformed = Vec::new();
    while let Some(atom) = state.workspace.pop_front() {
        transformed.push(atom);
    }

    for i in 1..=3 {
        let expected = Atom::expr(vec![
            Atom::sym("even"),
            Atom::num(i as i128),
        ]);
        assert!(transformed.contains(&expected), "Should have (even {})", i);
    }
}
