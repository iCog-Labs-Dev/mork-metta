//! Tests for boolean operators `and`, `or`, `not`, `xor`, `implies`
//! verified against PeTTa (Prolog) semantics.
//!
//! PeTTa Prolog implementation (metta.pl):
//!   and(A,B,C)   :- bool(A), bool(B), ( A == true -> C = B ; A == false -> C = false ).
//!   or(A,B,C)    :- bool(A), bool(B), ( A == true -> C = true ; A == false -> C = B ).
//!   not(A,B)     :- bool(A), ( A == true -> B = false ; A == false -> B = true ).
//!   xor(A,B,C)   :- bool(A), bool(B), ( A == B -> C = false ; C = true ).
//!   implies(A,B,C) :- bool(A), bool(B),
//!                      ( A == true -> ( B == true -> C = true ; B == false -> C = false )
//!                      ; A == false -> C = true ).
//!
//! Key: PeTTa translates (True|False) → (true|false) at parse time.
//! This runtime normalizes via Atom::sym() the same way.
//! Both silently fail on non-boolean args (no matching clause → ()).
use mork_metta::Runtime;

fn run(rt: &mut Runtime, code: &str) -> String {
    rt.eval_str(code)
        .unwrap()
        .map(|a| a.to_sexpr_string())
        .unwrap_or_else(|| "()".to_string())
}

fn run_err(rt: &mut Runtime, code: &str) -> String {
    rt.eval_str(code).unwrap_err()
}

// ====================================================================
// and — truth table
// PeTTa: and(true, true) = true, else false
// ====================================================================

#[test]
fn and_true_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and True True)"), "true");
}

#[test]
fn and_true_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and True False)"), "false");
}

#[test]
fn and_false_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and False True)"), "false");
}

#[test]
fn and_false_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and False False)"), "false");
}

// ====================================================================
// or — truth table
// PeTTa: or(true, _) = true, or(false, B) = B
// ====================================================================

#[test]
fn or_true_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(or True True)"), "true");
}

#[test]
fn or_true_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(or True False)"), "true");
}

#[test]
fn or_false_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(or False True)"), "true");
}

#[test]
fn or_false_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(or False False)"), "false");
}

// ====================================================================
// not — truth table
// PeTTa: not(true) = false, not(false) = true
// ====================================================================

#[test]
fn not_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(not True)"), "false");
}

#[test]
fn not_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(not False)"), "true");
}

// ====================================================================
// xor — truth table
// PeTTa: xor(A, B) = true if A != B
// ====================================================================

#[test]
fn xor_true_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(xor True False)"), "true");
}

#[test]
fn xor_false_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(xor False True)"), "true");
}

#[test]
fn xor_true_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(xor True True)"), "false");
}

#[test]
fn xor_false_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(xor False False)"), "false");
}

// ====================================================================
// implies — truth table
// PeTTa: implies(A, B) = false only if A=true and B=false
// ====================================================================

#[test]
fn implies_true_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(implies True True)"), "true");
}

#[test]
fn implies_true_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(implies True False)"), "false");
}

#[test]
fn implies_false_true() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(implies False True)"), "true");
}

#[test]
fn implies_false_false() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(implies False False)"), "true");
}

// ====================================================================
// Nested / compound expressions (real usage patterns from all 3 repos)
// ====================================================================

#[test]
fn not_and() {
    let mut rt = Runtime::new();
    // Pattern: (not (and ...)) — used in PeTTa-OpenPSI demands.metta
    assert_eq!(run(&mut rt, "!(not (and True True))"), "false");
    assert_eq!(run(&mut rt, "!(not (and True False))"), "true");
}

#[test]
fn and_not() {
    let mut rt = Runtime::new();
    // Pattern: (and (not A) B) — used in hill-climbing-helpers, HebbianCreation
    assert_eq!(run(&mut rt, "!(and (not True) False)"), "false");
    assert_eq!(run(&mut rt, "!(and (not False) True)"), "true");
}

#[test]
fn or_of_and() {
    let mut rt = Runtime::new();
    // Pattern: (or (and X Y) (and W Z)) — moses/neighborhood-sampling
    assert_eq!(run(&mut rt, "!(or (and True False) (and False True))"), "false");
    assert_eq!(run(&mut rt, "!(or (and True True) (and False True))"), "true");
}

#[test]
fn and_with_equality() {
    let mut rt = Runtime::new();
    // Pattern: (and (== A B) (< C D)) — extremely common in all 3 repos
    assert_eq!(run(&mut rt, "!(and (== 1 1) (== 2 2))"), "true");
    assert_eq!(run(&mut rt, "!(and (== 1 1) (== 1 2))"), "false");
    assert_eq!(run(&mut rt, "!(and (== 1 2) (== 2 2))"), "false");
}

#[test]
fn or_with_equality() {
    let mut rt = Runtime::new();
    // Pattern: (or (== A ()) (== B ())) — very common in all 3 repos
    // (e.g. checking if things are empty)
    assert_eq!(run(&mut rt, "!(or (== () ()) (== 1 2))"), "true");
    assert_eq!(run(&mut rt, "!(or (== () 1) (== () 2))"), "false");
    assert_eq!(run(&mut rt, "!(or (== 1 2) (== 3 4))"), "false");
}

#[test]
fn not_equal() {
    let mut rt = Runtime::new();
    // Pattern: (not (== X Y)) — most common negated pattern
    assert_eq!(run(&mut rt, "!(not (== 1 2))"), "true");
    assert_eq!(run(&mut rt, "!(not (== 1 1))"), "false");
}

#[test]
fn nested_and() {
    let mut rt = Runtime::new();
    // Pattern: (and A (and B C)) — PeTTa-OpenPSI modulator-updater-test
    assert_eq!(run(&mut rt, "!(and True (and True True))"), "true");
    assert_eq!(run(&mut rt, "!(and True (and True False))"), "false");
}

#[test]
fn complex_boolean_expression() {
    let mut rt = Runtime::new();
    // Pattern from metta-moses expand-deme:
    // (and (>= $val $low) (<= $val $high))
    assert_eq!(
        run(&mut rt, "!(and (>= 5 0) (<= 5 10))"),
        "true"
    );
    assert_eq!(
        run(&mut rt, "!(and (>= 5 0) (<= 5 3))"),
        "false"
    );
}

#[test]
fn if_with_and_condition() {
    let mut rt = Runtime::new();
    // Pattern: (if (and X Y) Then Else) — extremely common
    assert_eq!(run(&mut rt, "!(if (and True True) 10 20)"), "10");
    assert_eq!(run(&mut rt, "!(if (and True False) 10 20)"), "20");
}

#[test]
fn if_with_or_condition() {
    let mut rt = Runtime::new();
    // Pattern: (if (or X Y) Then Else) — common
    assert_eq!(run(&mut rt, "!(if (or False True) 10 20)"), "10");
    assert_eq!(run(&mut rt, "!(if (or False False) 10 20)"), "20");
}

#[test]
fn if_with_not_condition() {
    let mut rt = Runtime::new();
    // Pattern: (if (not X) Then Else) — common in tic-tac-toe, moses
    assert_eq!(run(&mut rt, "!(if (not True) 10 20)"), "20");
    assert_eq!(run(&mut rt, "!(if (not False) 10 20)"), "10");
}

#[test]
fn implies_in_condition() {
    let mut rt = Runtime::new();
    // Using implies within a conditional
    assert_eq!(run(&mut rt, "!(if (implies False True) yes no)"), "yes");
    assert_eq!(run(&mut rt, "!(if (implies True False) yes no)"), "no");
}

// ====================================================================
// Edge cases: non-boolean args silently fail (PeTTa behavior)
// ====================================================================

#[test]
fn and_non_bool_second_arg() {
    let mut rt = Runtime::new();
    // PeTTa: bool(42) fails → no result → ()
    assert_eq!(run(&mut rt, "!(and True 42)"), "()");
    assert_eq!(run(&mut rt, "!(and True (a b c))"), "()");
}

#[test]
fn and_non_bool_first_arg() {
    let mut rt = Runtime::new();
    // PeTTa: bool(42) fails → no result
    assert_eq!(run(&mut rt, "!(and 42 True)"), "()");
}

#[test]
fn or_non_bool_args() {
    let mut rt = Runtime::new();
    // PeTTa: bool arguments fail
    assert_eq!(run(&mut rt, "!(or True 42)"), "()");
    assert_eq!(run(&mut rt, "!(or 42 True)"), "()");
}

#[test]
fn not_non_bool_args() {
    let mut rt = Runtime::new();
    // PeTTa: bool(42) fails
    assert_eq!(run(&mut rt, "!(not 42)"), "()");
    assert_eq!(run(&mut rt, "!(not ())"), "()");
    assert_eq!(run(&mut rt, "!(not hello)"), "()");
}

#[test]
fn xor_non_bool_args() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(xor True 42)"), "()");
    assert_eq!(run(&mut rt, "!(xor 42 True)"), "()");
}

#[test]
fn implies_non_bool_args() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(implies True 42)"), "()");
    assert_eq!(run(&mut rt, "!(implies 42 True)"), "()");
}

// ====================================================================
// Edge cases: both args non-bool
// ====================================================================

#[test]
fn both_non_bool() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and 42 hello)"), "()");
    assert_eq!(run(&mut rt, "!(or 42 ())"), "()");
    assert_eq!(run(&mut rt, "!(xor 42 hello)"), "()");
    assert_eq!(run(&mut rt, "!(implies () 42)"), "()");
}

// ====================================================================
// Edge cases: extra args (arity mismatch)
// PeTTa: and/3 is the registered predicate, but (and A B) → 2 args + output
// Runtime: and/2 registered. Extra args just don't match any clause → ()
// ====================================================================

#[test]
fn and_extra_args() {
    let mut rt = Runtime::new();
    // Runtime has and/2. Arity 3: no matching clause, data-list eval → (and true true true)
    // Arity 1: < registered arity, partial application → (partial and (true))
    assert_eq!(run(&mut rt, "!(and True True True)"), "(and true true true)");
    assert_eq!(run(&mut rt, "!(and True)"), "(partial and (true))");
}

#[test]
fn or_extra_args() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(or True True True)"), "(or true true true)");
    assert_eq!(run(&mut rt, "!(or True)"), "(partial or (true))");
}

#[test]
fn not_extra_args() {
    let mut rt = Runtime::new();
    // Runtime has not/1 — arity 2: data-list, arity 0: partial application
    assert_eq!(run(&mut rt, "!(not True True)"), "(not true true)");
    assert_eq!(run(&mut rt, "!(not)"), "(partial not ())");
}

// ====================================================================
// Lowercase booleans also work (both PeTTa and runtime normalize)
// ====================================================================

#[test]
fn lowercase_booleans() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and true true)"), "true");
    assert_eq!(run(&mut rt, "!(and true false)"), "false");
    assert_eq!(run(&mut rt, "!(or false true)"), "true");
    assert_eq!(run(&mut rt, "!(not true)"), "false");
    assert_eq!(run(&mut rt, "!(not false)"), "true");
    assert_eq!(run(&mut rt, "!(xor true false)"), "true");
    assert_eq!(run(&mut rt, "!(implies false true)"), "true");
}

// ====================================================================
// Mixed case normalizes the same
// ====================================================================

#[test]
fn mixed_case_booleans() {
    let mut rt = Runtime::new();
    assert_eq!(run(&mut rt, "!(and true True)"), "true");
    assert_eq!(run(&mut rt, "!(and False true)"), "false");
    assert_eq!(run(&mut rt, "!(or True false)"), "true");
    assert_eq!(run(&mut rt, "!(not False)"), "true");
}

// ====================================================================
// Market: usage pattern with (not (and ...)) deeply nested
// ====================================================================

#[test]
fn deeply_nested_boolean() {
    let mut rt = Runtime::new();
    // Pattern from hill-climbing-helpers:
    // (and (and (not $hasImproved) (not $lastChance)) (not $xOver))
    assert_eq!(
        run(&mut rt, "!(and (and (not False) (not True)) (not False))"),
        "false"
    );
    assert_eq!(
        run(&mut rt, "!(and (and (not True) (not False)) (not True))"),
        "false"
    );
}
