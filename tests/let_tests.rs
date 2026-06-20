//! Tests for `let` based on PeTTa semantics verified against metta-moses patterns.
//!
//! PeTTa `let` semantics (from Prolog impl):
//!   let = [Pat, Val, In] -> translate_expr(Pat, Gp, Pv),
//!                            translate_expr(Val, Gv, V),
//!                            translate_expr(In,  Gi, Out),
//!                            append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
//!
//! Means: unify Pat with the result of Val, then evaluate In.
//! Pat can be: $var, ($a $b), (Ctor $a $b), (), $_
//!
//! All known discrepancies from PeTTa have been fixed:
//! - Shadowing now correctly fails (single-assignment semantics)
//! - Empty pat + non-empty value still returns () (benign mismatch)
//! - $_ treated as named var now fails (truly anonymous in PeTTa)

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
// Pattern 1: let $var $val $body (single variable binding)
// Most common pattern in moses: (let $score ...)
// ====================================================================

#[test]
fn let_bind_var_to_number() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x 42 $x) -> 42
    assert_eq!(run(&mut rt, "!(let $x 42 $x)"), "42");
}

#[test]
fn let_bind_var_to_expression() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x (+ 1 2) $x) -> 3
    assert_eq!(run(&mut rt, "!(let $x (+ 1 2) $x)"), "3");
}

#[test]
fn let_bind_var_to_symbol_list() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x (a b c) $x) -> (a b c)
    assert_eq!(run(&mut rt, "!(let $x (a b c) $x)"), "(a b c)");
}

#[test]
fn let_body_uses_bound_var() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x 10 (+ $x $x)) -> 20
    assert_eq!(run(&mut rt, "!(let $x 10 (+ $x $x))"), "20");
}

#[test]
fn let_body_uses_bound_var_twice() {
    let mut rt = Runtime::new();
    // PeTTa: (let $xs (a b c) (cons-atom $xs $xs)) -> ((a b c) a b c)
    assert_eq!(
        run(&mut rt, "!(let $xs (a b c) (cons-atom $xs $xs))"),
        "((a b c) a b c)"
    );
}

// ====================================================================
// Pattern 2: let ($h $t) (decons-atom $list) $body
// Used in: tic-tac-toe-helpers.metta, feature-selection-helpers.metta, bscore.metta
// ====================================================================

#[test]
fn let_destructure_decons_head() {
    let mut rt = Runtime::new();
    // PeTTa: (let ($h $t) (decons-atom (a b c)) $h) -> a
    assert_eq!(
        run(&mut rt, "!(let ($h $t) (decons-atom (a b c)) $h)"),
        "a"
    );
}

#[test]
fn let_destructure_decons_tail() {
    let mut rt = Runtime::new();
    // PeTTa: (let ($h $t) (decons-atom (a b c)) $t) -> (b c)
    assert_eq!(
        run(&mut rt, "!(let ($h $t) (decons-atom (a b c)) $t)"),
        "(b c)"
    );
}

#[test]
fn let_destructure_decons_single_tail_is_empty() {
    let mut rt = Runtime::new();
    // PeTTa: (let ($h $t) (decons-atom (x)) $t) -> ()
    assert_eq!(
        run(&mut rt, "!(let ($h $t) (decons-atom (x)) $t)"),
        "()"
    );
}

// ====================================================================
// Pattern 3: let (Ctor $v1 $v2 ...) $val $body
// Used in: metapopulation.metta, sggp-algorithm-with-tests.metta, build-knobs.metta
// ====================================================================

#[test]
fn let_destructure_constructor() {
    let mut rt = Runtime::new();
    // PeTTa: (let (mkPair $a $b) (mkPair 1 2) $a) -> 1
    assert_eq!(
        run(&mut rt, "!(let (mkPair $a $b) (mkPair 1 2) $a)"),
        "1"
    );
}

#[test]
fn let_destructure_constructor_second() {
    let mut rt = Runtime::new();
    // PeTTa: (let (mkPair $a $b) (mkPair 1 2) $b) -> 2
    assert_eq!(
        run(&mut rt, "!(let (mkPair $a $b) (mkPair 1 2) $b)"),
        "2"
    );
}

// ====================================================================
// Pattern 4: let ($v1 $v2) (expr1 expr2) $body (multi-value from pair)
// Used in: metapopulation.metta, cross-top-one-helpers.metta, cscore.metta
// ====================================================================

#[test]
fn let_destructure_two_values() {
    let mut rt = Runtime::new();
    // PeTTa: (let ($a $b) (10 20) (+ $a $b)) -> 30
    assert_eq!(run(&mut rt, "!(let ($a $b) (10 20) (+ $a $b))"), "30");
}

#[test]
fn let_destructure_three_values() {
    let mut rt = Runtime::new();
    // PeTTa: (let ($a $b $c) (1 2 3) (+ (+ $a $b) $c)) -> 6
    assert_eq!(
        run(&mut rt, "!(let ($a $b $c) (1 2 3) (+ (+ $a $b) $c))"),
        "6"
    );
}

// ====================================================================
// Pattern 5: let () $val $body (no binding, sequence)
// Used in: pge-eda.metta, pge2.metta, sggp-algorithm-with-tests.metta
#[test]
fn let_empty_pat_with_empty_value() {
    let mut rt = Runtime::new();
    // PeTTa: (let () () 99) -> 99 (() unifies with ())
    assert_eq!(run(&mut rt, "!(let () () 99)"), "99");
}

// ====================================================================
// Pattern 6: let $var $val (let ...) — nested let
// Used in: neighborhood-sampling.metta (5 deep), tic-tac-toe-helpers.metta
// ====================================================================

#[test]
fn let_nested_sequential() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x 10 (let $y 20 (+ $x $y))) -> 30
    assert_eq!(
        run(&mut rt, "!(let $x 10 (let $y 20 (+ $x $y)))"),
        "30"
    );
}

#[test]
fn let_nested_inner_binding_as_value() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x (let $y 10 (+ $y 5)) (* $x 2)) -> 30
    assert_eq!(
        run(&mut rt, "!(let $x (let $y 10 (+ $y 5)) (* $x 2))"),
        "30"
    );
}

// ====================================================================
// Pattern 7: let with if (conditional body)
// Used in: merge-demes.metta, tic-tac-toe-helpers.metta, expand-deme.metta
// ====================================================================

#[test]
fn let_with_if_big() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x 10 (if (> $x 5) big small)) -> big
    assert_eq!(
        run(&mut rt, "!(let $x 10 (if (> $x 5) big small))"),
        "big"
    );
}

#[test]
fn let_with_if_empty_check() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x () (if (== $x ()) empty nonempty)) -> empty
    assert_eq!(
        run(&mut rt, "!(let $x () (if (== $x ()) empty nonempty))"),
        "empty"
    );
}

// ====================================================================
// Pattern 8: let with function call as value (bscore.metta, fitness.metta)
// ====================================================================

#[test]
fn let_with_car_atom() {
    let mut rt = Runtime::new();
    // PeTTa: (let $result (car-atom (x y)) $result) -> x
    assert_eq!(
        run(&mut rt, "!(let $result (car-atom (x y)) $result)"),
        "x"
    );
}

// ====================================================================
// Pattern 9: let with side-effect discard (let $_ ...)
// Used in: expand-deme.metta, general-helpers.metta, sge-and-tests.metta
// ====================================================================

#[test]
fn let_underscore_discards_value() {
    let mut rt = Runtime::new();
    // PeTTa: (let $_ 42 99) -> 99
    assert_eq!(run(&mut rt, "!(let $_ 42 99)"), "99");
}

// ====================================================================
// Pattern 10: let used in recursive function (decons + recurse)
// From moses: tic-tac-toe-helpers.metta, feature-selection-helpers.metta
// ====================================================================

#[test]
fn let_in_recursive_function() {
    let mut rt = Runtime::new();
    let _ = rt.eval_str(
        "(= (sum-list $xs) (if (== $xs ()) 0
            (let ($h $t) (decons-atom $xs) (+ $h (sum-list $t)))))",
    );
    assert_eq!(run(&mut rt, "!(sum-list (1 2 3))"), "6");
}

// ====================================================================
// Pattern 11: Nested multi-let (like let* but with nested let)
// From neighborhood-sampling.metta:
//   (let $multips ... (let $instExp ... (let $listNeighbors ... ...)))
// ====================================================================

#[test]
fn let_triple_nested() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let $a 1 (let $b 2 (let $c 3 (+ (+ $a $b) $c))))",
    );
    assert_eq!(r, "6");
}

// ====================================================================
// Pattern 12: let with pair destructure then use both parts
// From merge-demes.metta: (let ($headDeme $tailDeme) (decons-atom $demes) ...)
// ====================================================================

#[test]
fn let_decons_then_rebuild() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (a b c)) (cons-atom $h $t))",
    );
    assert_eq!(r, "(a b c)");
}

// ====================================================================
// Pattern 13: let with quote to prevent eval
// ====================================================================

#[test]
fn let_bind_quoted_expr() {
    let mut rt = Runtime::new();
    // PeTTa: (let $x (quote (a b c)) $x) => (a b c) processed
    // Actually PeTTa doesn't handle quote as the `!` expression evaluates its arg...
    // Let me skip this and check
    let r = run(&mut rt, "!(let $x (quote (a b c)) $x)");
    // quote returns the argument unevaluated: (a b c)
    assert_eq!(r, "(a b c)");
}

// ====================================================================
// Pattern 14: let with empty tuple in body (used in pge-eda.metta)
// ====================================================================

#[test]
fn let_empty_body_returns_none() {
    let mut rt = Runtime::new();
    // (let $x 42 ()) -> ()
    let r = run(&mut rt, "!(let $x 42 ())");
    assert_eq!(r, "()");
}

// ====================================================================
// Pattern 15: let with constructor pattern matching (AND, OR, etc.)
// PeTTa: (let (AND $a $b) (AND x y) $b) → y
// ====================================================================

#[test]
fn let_constructor_pattern_matches_second_field() {
    let mut rt = Runtime::new();
    let r = run(&mut rt, "!(let (AND $a $b) (AND x y) $b)");
    assert_eq!(r, "y");
}

#[test]
fn let_constructor_pattern_swaps_fields_in_body() {
    let mut rt = Runtime::new();
    let r = run(&mut rt, "!(let (AND $a $b) (AND x y) (AND $b $a))");
    assert_eq!(r, "(AND y x)");
}

// ====================================================================
// Pattern 16: let with destructure of proper list (not pair) — fails
// PeTTa: (let ($a $b) (1) 99) fails — length mismatch
// ====================================================================

#[test]
fn let_length_mismatch_short_list_silent_fail() {
    let mut rt = Runtime::new();
    // Pattern expects 2 elems, value has 1 → silent fail (returns ())
    let r = run(&mut rt, "!(let ($a $b) (1) 99)");
    assert_eq!(r, "()");
}

#[test]
fn let_length_mismatch_long_list_silent_fail() {
    let mut rt = Runtime::new();
    // Pattern expects 2 elems, value has 3 → silent fail (returns ())
    let r = run(&mut rt, "!(let ($a $b) (1 2 3) 99)");
    assert_eq!(r, "()");
}

#[test]
fn let_consatom_destructure_silent_fail() {
    let mut rt = Runtime::new();
    // cons-atom returns 3-element list (x y z), pattern ($a $b) expects pair → fail
    let r = run(&mut rt, "!(let ($a $b) (cons-atom x (y z)) $a)");
    assert_eq!(r, "()");
}

// ====================================================================
// Pattern 17: let with variable shadowing — PeTTa matches (was discrepancy)
// PeTTa: (let $x 10 (let $x 20 $x)) fails — can't unify X=10, X=20
// Runtime: now also fails (single-assignment), matching PeTTa
// ====================================================================

#[test]
fn let_shadowing_silent_fail() {
    let mut rt = Runtime::new();
    // Single-assignment: binding $x=10 then $x=20 fails
    let r = run(&mut rt, "!(let $x 10 (let $x 20 $x))");
    assert_eq!(r, "()");
}

// ====================================================================
// Pattern 18: let with empty pattern and non-empty value — PeTTa match
// PeTTa: (let () 42 99) fails — [] = 42 unification fails
// Runtime: same — silent fail, returns ()
// ====================================================================

#[test]
fn let_empty_pat_with_nonempty_value() {
    let mut rt = Runtime::new();
    // Runtime silently discards the mismatch (() vs 42)
    let r = run(&mut rt, "!(let () 42 99)");
    assert_eq!(r, "()");
}

// ====================================================================
// Pattern 19: let $_ is truly anonymous — cannot reference across nested let
// PeTTa: (let $_ 42 (let $_ 99 (+ $_ $_))) crashes — _ is anonymous
// Runtime: now also fails (truly anonymous), matching PeTTa
// ====================================================================

#[test]
fn let_anonymous_underscore_silent_fail() {
    let mut rt = Runtime::new();
    // $_ is anonymous — no value carried forward to body
    let r = run(&mut rt, "!(let $_ 42 (let $_ 99 (+ $_ $_)))");
    assert_eq!(r, "()");
}
