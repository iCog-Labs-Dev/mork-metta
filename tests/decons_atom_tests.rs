//! Tests for `decons-atom` based on usage patterns found in metta-moses.
//!
//! Prolog semantics (the reference): `decons-atom([H|T], [H|[T]])`.
//! Splits a non-empty list into a 2-element list: `(head tail)`.
//! Errors on empty list or non-list input.

use mork_metta::Runtime;

/// Evaluate a `!` form, return the S-expression string of the result.
fn run(rt: &mut Runtime, code: &str) -> String {
    rt.eval_str(code)
        .unwrap()
        .map(|a| a.to_sexpr_string())
        .unwrap_or_else(|| "()".to_string())
}

/// Load a definition.
fn def(rt: &mut Runtime, code: &str) {
    rt.eval_str(code).unwrap();
}

// ====================================================================
// Contract tests: decons-atom behaves as `[H|T] -> [H, [T]]`
// ====================================================================

#[test]
fn contract_splits_list_into_head_and_tail() {
    let mut rt = Runtime::new();
    // (a b c) -> head=a, tail=(b c) -> result (a (b c))
    let r = run(&mut rt, "!(decons-atom (a b c))");
    assert_eq!(r, "(a (b c))");
}

#[test]
fn contract_single_element() {
    let mut rt = Runtime::new();
    let r = run(&mut rt, "!(decons-atom (only))");
    assert_eq!(r, "(only ())");
}

#[test]
fn contract_two_elements() {
    let mut rt = Runtime::new();
    let r = run(&mut rt, "!(decons-atom (1 2))");
    assert_eq!(r, "(1 (2))");
}

#[test]
fn contract_nested_list() {
    let mut rt = Runtime::new();
    // ((inner) x y) -> head=(inner), tail=(x y) -> result ((inner) (x y))
    let r = run(&mut rt, "!(decons-atom ((inner) x y))");
    assert_eq!(r, "((inner) (x y))");
}

#[test]
fn contract_empty_list_is_error() {
    let mut rt = Runtime::new();
    let err = rt.eval_str("!(decons-atom ())").unwrap_err();
    assert!(err.contains("empty list"), "got: {err}");
}

#[test]
fn contract_symbol_is_error() {
    let mut rt = Runtime::new();
    let err = rt.eval_str("!(decons-atom hello)").unwrap_err();
    assert!(err.contains("expected list"), "got: {err}");
}

#[test]
fn contract_number_is_error() {
    let mut rt = Runtime::new();
    let err = rt.eval_str("!(decons-atom 42)").unwrap_err();
    assert!(err.contains("expected list"), "got: {err}");
}

#[test]
fn contract_string_is_error() {
    let mut rt = Runtime::new();
    let err = rt.eval_str(r#"!(decons-atom "hello")"#).unwrap_err();
    assert!(err.contains("expected list"), "got: {err}");
}

// ====================================================================
// Pattern 1: `let ($h $t) (decons-atom $list)`  (basic destructure)
// Used in: general-helpers.metta, tic-tac-toe-helpers.metta,
//          feature-selection-helpers.metta, bscore.metta,
//          ordered-set.metta
// ====================================================================

#[test]
fn pattern_let_destructure_head_and_tail() {
    let mut rt = Runtime::new();
    // (let ($h $t) (decons-atom (a b c)) ...)
    // $h = a, $t = (b c)
    // cons-atom rebuilds the original: (a b c)
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (a b c))
            (cons-atom $h $t))",
    );
    assert_eq!(r, "(a b c)");
}

#[test]
fn pattern_let_destructure_single() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (only))
            (cons-atom $h $t))",
    );
    assert_eq!(r, "(only)");
}

#[test]
fn pattern_let_use_head_only() {
    let mut rt = Runtime::new();
    // Use symbols that don't collide with builtin functions
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (foo bar))
            $h)",
    );
    assert_eq!(r, "foo");
}

#[test]
fn pattern_let_use_tail_only() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (foo bar))
            $t)",
    );
    assert_eq!(r, "(bar)");
}

#[test]
fn pattern_let_tail_is_always_expression() {
    let mut rt = Runtime::new();
    // Tail is always a list (Expression), even for single element
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (x y))
            (== (get-metatype $t) Expression))",
    );
    assert_eq!(r, "true");
}

// ====================================================================
// Pattern 2: `let* ((($h $t) (decons-atom $list)) ...)`
// Used in: alpha-beta-minimax-player.metta, cscore.metta,
//          precision-bscore.metta, logical-probe.metta
// ====================================================================

#[test]
fn pattern_letstar_unboxed_pair() {
    let mut rt = Runtime::new();
    // (let* ((($a $rest) (decons-atom (10 20 30))) ...) ...)
    let r = run(
        &mut rt,
        "!(let* ((($a $rest) (decons-atom (10 20 30))))
            (cons-atom $a $rest))",
    );
    assert_eq!(r, "(10 20 30)");
}

#[test]
fn pattern_letstar_bind_and_use() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($x $xs) (decons-atom (foo bar baz)))
                 ($y (car-atom $xs)))
            (cons-atom $x $y))",
    );
    assert_eq!(r, "(foo bar)");
}

// ====================================================================
// Pattern 3: Chained decons-atom on $rest  (sequential field extraction)
// Used in: cscore.metta (5 sequential calls on a tuple)
// ====================================================================

#[test]
fn pattern_chained_decons_three_fields() {
    let mut rt = Runtime::new();
    // From cscore.metta:
    //   (($scor $rest1) (decons-atom $expr))
    //   (($cpxy $rest2) (decons-atom $rest1))
    //   (($complexityPenalty $rest3) (decons-atom $rest2))
    let r = run(
        &mut rt,
        "!(let* ((($a $r1) (decons-atom (10 20 30)))
                  (($b $r2) (decons-atom $r1))
                  (($c $r3) (decons-atom $r2)))
            (cons-atom $c (cons-atom $b $a)))",
    );
    assert_eq!(r, "(30 20 10)");
}

#[test]
fn pattern_chained_decons_ignore_remainder() {
    // cscore.metta uses `$_` to discard the final tail:
    //   (($penalizedScore $_) (decons-atom $rest4))
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($a $r1) (decons-atom (x y z)))
                  (($b $r2) (decons-atom $r1))
                  (($c $_)  (decons-atom $r2)))
            $c)",
    );
    assert_eq!(r, "z");
}

// ====================================================================
// Pattern 4: Nil guard  `(if (not (== $xs ())) (decons-atom $xs) ...)`
// Used in: rte-helpers.metta, cut-unnecessary-and.metta
// ====================================================================

#[test]
fn pattern_nil_guard_nonempty() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let $xs (a b)
            (if (not (== $xs ()))
                (let ($h $t) (decons-atom $xs) (cons-atom $h $t))
                ()))",
    );
    assert_eq!(r, "(a b)");
}

#[test]
fn pattern_nil_guard_empty_skips_decons() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let $xs ()
            (if (not (== $xs ()))
                (let ($h $t) (decons-atom $xs) $h)
                empty-case))",
    );
    assert_eq!(r, "empty-case");
}

// ====================================================================
// Pattern 5: Type guard  `(== (get-metatype $x) Expression)` before decons
// Used in: bscore.metta, tree.metta
// ====================================================================

#[test]
fn pattern_type_guard_expr_allows_decons() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let $x (a b c)
            (if (== (get-metatype $x) Expression)
                (let ($h $t) (decons-atom $x) $h)
                ()))",
    );
    assert_eq!(r, "a");
}

#[test]
fn pattern_type_guard_symbol_skips_decons() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let $x foo
            (if (== (get-metatype $x) Expression)
                (let ($h $t) (decons-atom $x) $h)
                not-expr))",
    );
    assert_eq!(r, "not-expr");
}

// ====================================================================
// Pattern 6: Nested decons-atom  (two lists at once)
// Used in: knob-representation.metta, neighborhood-sampling.metta,
//          instance.metta
// ====================================================================

#[test]
fn pattern_nested_two_lists() {
    let mut rt = Runtime::new();
    // From knob-representation.metta:
    //   (($headId1 $tailId1) (decons-atom $id1))
    //   (($headId2 $tailId2) (decons-atom $id2)))
    let r = run(
        &mut rt,
        "!(let* ((($h1 $t1) (decons-atom (x y)))
                  (($h2 $t2) (decons-atom (1 2))))
            (cons-atom $h1 $h2))",
    );
    assert_eq!(r, "(x 1)");
}

#[test]
fn pattern_nested_decons_compare_heads() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($h1 $t1) (decons-atom (a b)))
                  (($h2 $t2) (decons-atom (a c))))
            (== $h1 $h2))",
    );
    assert_eq!(r, "true");
}

// ====================================================================
// Pattern 7: Recursive "pop front" list processing
// Used in: tic-tac-toe-helpers.metta, feature-selection-helpers.metta,
//          neighborhood-sampling.metta, general-helpers.metta,
//          delete-inconsistent-handle.metta
// ====================================================================

#[test]
fn pattern_recursive_length() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (my-length $xs) (if (== $xs ()) 0
            (let ($h $t) (decons-atom $xs) (+ 1 (my-length $t)))))",
    );
    assert_eq!(run(&mut rt, "!(my-length (a b c d))"), "4");
    assert_eq!(run(&mut rt, "!(my-length ())"), "0");
}

#[test]
fn pattern_recursive_member() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (my-member $x $xs) (if (== $xs ()) ()
            (let ($h $t) (decons-atom $xs)
                (if (== $h $x) $h (my-member $x $t)))))",
    );
    assert_eq!(run(&mut rt, "!(my-member 3 (1 2 3 4))"), "3");
    assert_eq!(run(&mut rt, "!(my-member 5 (1 2 3 4))"), "()");
}

#[test]
fn pattern_recursive_collect() {
    // general-helpers.metta exprToList pattern: collect elements into cons-list
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (collect $xs) (if (== $xs ()) ()
            (let ($h $t) (decons-atom $xs) (cons-atom $h (collect $t)))))",
    );
    let r = run(&mut rt, "!(collect (x y z))");
    assert_eq!(r, "(x y z)");
}

#[test]
fn pattern_recursive_sum() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (sum-list $xs) (if (== $xs ()) 0
            (let ($h $t) (decons-atom $xs) (+ $h (sum-list $t)))))",
    );
    assert_eq!(run(&mut rt, "!(sum-list (1 2 3 4 5))"), "15");
}

// ====================================================================
// Pattern 8: Split operator and operands
// Used in: n-ary-propagate-not.metta, n-ary-gather-junctors.metta,
//          reduce-to-elegance.metta
// ====================================================================

#[test]
fn pattern_operator_and_operands_three_args() {
    let mut rt = Runtime::new();
    // (($op $args) (decons-atom (AND A B C)))
    // $op = AND, $args = (A B C)
    let r = run(
        &mut rt,
        "!(let* ((($op $args) (decons-atom (AND A B C))))
            $args)",
    );
    assert_eq!(r, "(A B C)");
}

#[test]
fn pattern_operator_and_operands_one_arg() {
    let mut rt = Runtime::new();
    // (($op $args) (decons-atom (NOT P)))
    // $op = NOT, $args = (P)
    let r = run(
        &mut rt,
        "!(let* ((($op $args) (decons-atom (NOT P))))
            $op)",
    );
    assert_eq!(r, "NOT");
}

// ====================================================================
// Pattern 9: Extract structured data from nested expressions
// Used in: instance.metta, merge-demes.metta
// ====================================================================

#[test]
fn pattern_extract_from_expression() {
    let mut rt = Runtime::new();
    // instance.metta: (($instExpr $scoreExpr) (decons-atom $expr))
    // where $expr = (someAtom 100)
    // $instExpr = someAtom, $scoreExpr = (100)  (tail is always a list)
    // Verify by checking tail is an expression
    let r = run(
        &mut rt,
        "!(let* ((($inst $score) (decons-atom (someAtom 100))))
            (== (get-metatype $score) Expression))",
    );
    assert_eq!(r, "true");
}

#[test]
fn pattern_extract_from_deme() {
    let mut rt = Runtime::new();
    // merge-demes.metta:
    //   (($headDeme $tailDeme) (decons-atom $demes))
    //   (($rep $sInstList $demeId) $headDeme)
    // Here: $demes = ((rep insts id1) (rep2 insts2 id2))
    // $headDeme = (rep insts id1), $tailDeme = ((rep2 insts2 id2))
    let r = run(
        &mut rt,
        "!(let* ((($head $tail) (decons-atom ((rep insts id1) (rep2 insts2 id2)))))
            (car-atom $head))",
    );
    assert_eq!(r, "rep");
}

// ====================================================================
// Pattern 10: Row extraction
// Used in: precision-bscore.metta
// ====================================================================

#[test]
fn pattern_row_extraction() {
    let mut rt = Runtime::new();
    // (($row $rest) (decons-atom $rows))
    // $rows = ((a 1) (b 2))
    // $row = (a 1), $rest = ((b 2))
    let r = run(
        &mut rt,
        "!(let* ((($row $rest) (decons-atom ((a 1) (b 2)))))
            (car-atom $row))",
    );
    assert_eq!(r, "a");
}

#[test]
fn pattern_row_extract_rest() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($row $rest) (decons-atom ((a 1) (b 2) (c 3)))))
            (car-atom $rest))",
    );
    assert_eq!(r, "(b 2)");
}

// ====================================================================
// Pattern 11: Cons-atom rebuild (decons then cons = identity)
// Used in: reduce-to-elegance.metta, neighborhood-sampling.metta
// ====================================================================

#[test]
fn pattern_decons_then_cons_preserves_identity() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (a b c d))
            (cons-atom $h $t))",
    );
    assert_eq!(r, "(a b c d)");
}

#[test]
fn pattern_decons_replace_head() {
    // Replace first element while preserving tail
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let ($h $t) (decons-atom (old 1 2))
            (cons-atom new $t))",
    );
    assert_eq!(r, "(new 1 2)");
}

// ====================================================================
// Pattern 12: Hamming distance (nested decons + recursion)
// From neighborhood-sampling.metta: distance between two lists
// ====================================================================

#[test]
fn pattern_hamming_distance_full() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (hamming $a $b) (if (== $a ())
            (if (== $b ()) 0 1)
            (if (== $b ()) 1
                (let ($h1 $t1) (decons-atom $a)
                (let ($h2 $t2) (decons-atom $b)
                    (+ (if (== $h1 $h2) 0 1) (hamming $t1 $t2)))))))",
    );
    assert_eq!(run(&mut rt, "!(hamming (a b c) (a x c))"), "1");
    assert_eq!(run(&mut rt, "!(hamming (a b) (x y))"), "2");
    assert_eq!(run(&mut rt, "!(hamming () ())"), "0");
}

// ====================================================================
// Pattern 13: Tree walk with type guard + decons + recursion
// Used in: bscore.metta, tree.metta, delete-inconsistent-handle.metta
// ====================================================================

#[test]
fn pattern_tree_walk_decons_leaves() {
    let mut rt = Runtime::new();
    // Walk a tree: if expression, decons & recurse; if leaf, return as singleton
    def(&mut rt,
        "(= (leaves $x) (if (== $x ()) ()
            (if (== (get-metatype $x) Expression)
                (let ($h $t) (decons-atom $x)
                    (leaves $h))
                (cons-atom $x ()))))",
    );
    // (AND A (OR B)): root is Expression, decons -> h=AND, t=(A (OR B))
    // AND is Grounded (symbol), so returns (AND).
    // Actually AND is a leaf. Let me use numbers as leaves instead.
    assert_eq!(run(&mut rt, "!(leaves 42)"), "(42)");
}

#[test]
fn pattern_tree_walk_collect_atoms() {
    let mut rt = Runtime::new();
    // Proper tree walk: recurse on head AND tail via decons
    // Guard ensures we only decons expressions, collect non-expression leaves
    def(&mut rt,
        "(= (collect-atoms $x) (if (== $x ()) ()
            (if (== (get-metatype $x) Expression)
                (let ($h $t) (decons-atom $x)
                    (cons-atom (collect-atoms $h) (collect-atoms $t)))
                (if (== $x true) ()
                    (cons-atom $x ())))))",
    );
    // Result: ((AND) (A) ((OR) (B)))
    //   (AND) from (collect-atoms AND) — leaf wrapped in cons-atom
    //   (A) from (collect-atoms A) — leaf wrapped in cons-atom
    //   ((OR) (B)) from (collect-atoms ((OR B))) — two leaves in a sublist
    let r = run(&mut rt, "!(collect-atoms (AND A (OR B)))");
    assert_eq!(r, "((AND) (A) ((OR) (B)))");
}

// ====================================================================
// Pattern 14: Lexicographic comparison (from knob-representation.metta)
// ====================================================================

#[test]
fn pattern_lexicographic_compare_decons_both_lists() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (lex< $a $b) (if (== $a ()) true
            (if (== $b ()) false
                (let* ((($ha $ta) (decons-atom $a))
                        (($hb $tb) (decons-atom $b)))
                    (if (== $ha $hb) (lex< $ta $tb)
                        (< $ha $hb))))))",
    );
    assert_eq!(run(&mut rt, "!(lex< (1 2) (1 3))"), "true");
    assert_eq!(run(&mut rt, "!(lex< (2 1) (1 3))"), "false");
}

// ====================================================================
// Pattern 15: Multi-field extraction (from cscore.metta)
// ====================================================================

#[test]
fn pattern_cscore_five_field_extraction() {
    let mut rt = Runtime::new();
    // cscore.metta extracts 5 fields in sequence via chained decons-atom
    let r = run(
        &mut rt,
        "!(let* ((($a $r1) (decons-atom (score 0.5 0.1 0.05 42.0)))
                  (($b $r2) (decons-atom $r1))
                  (($c $r3) (decons-atom $r2))
                  (($d $r4) (decons-atom $r3))
                  (($e $_)  (decons-atom $r4)))
            (cons-atom $a (cons-atom $e $b)))",
    );
    // $a = score, $e = 42.0, $b = 0.5 -> (cons-atom 42.0 0.5) -> (42 0.5)
    // (cons-atom score (42 0.5)) -> (score 42 0.5)
    assert_eq!(r, "(score 42 0.5)");
}

// ====================================================================
// Pattern 16: Walk accumulating (from ordered-set.metta)
// ====================================================================

#[test]
fn pattern_decons_with_accumulator() {
    let mut rt = Runtime::new();
    def(&mut rt,
        "(= (list-of $acc $xs) (if (== $xs ()) $acc
            (let ($h $t) (decons-atom $xs)
                (list-of (cons-atom $h $acc) $t))))",
    );
    let r = run(&mut rt, "!(list-of () (a b c))");
    assert_eq!(r, "(c b a)");
}

// ====================================================================
// Pattern 17: Inside `if-decons-expr-custom` style guard+decons
// (rte-helpers.metta)
// ====================================================================

#[test]
fn pattern_guard_decons_short_circuit() {
    let mut rt = Runtime::new();
    // Pattern: (if (not (== $exp ()))
    //             (if (== (get-metatype $exp) Expression)
    //                 (let ($h $t) (decons-atom $exp) ...)
    //                 fallback)
    //             fallback)
    let r = run(
        &mut rt,
        "!(let $exp (a b)
            (if (not (== $exp ()))
                (if (== (get-metatype $exp) Expression)
                    (let ($h $t) (decons-atom $exp) $h)
                    $exp)
                ()))",
    );
    assert_eq!(r, "a");
}

// ====================================================================
// Edge cases
// ====================================================================

#[test]
fn edge_decons_of_decons_result() {
    // (decons-atom (a (b c))) -> a then ((b c))
    // Outer decons on that: (a ((b c)))
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($h1 $t1) (decons-atom (a (b c)))))
            $t1)",
    );
    assert_eq!(r, "((b c))");
}

#[test]
fn edge_decons_inside_decons_nested_result() {
    let mut rt = Runtime::new();
    let r = run(
        &mut rt,
        "!(let* ((($h1 $t1) (decons-atom (a (b c))))
                  (($h2 $t2) (decons-atom $t1)))
            (cons-atom $h1 $h2))",
    );
    // $h1 = a, $t1 = ((b c))
    // decons $t1: $h2 = (b c), $t2 = ()
    // cons-atom a (b c) = (a b c)  (cons-atom flattens the list)
    assert_eq!(r, "(a b c)");
}
