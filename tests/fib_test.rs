use mork_metta::Runtime;
use mork_metta::atom::Atom;
use mork_metta::compile::compile_definition;
use mork_metta::env::Env;
use mork_metta::eval::eval;
use mork_metta::func::FnTable;
use mork_metta::builtins::register_builtins;
use mork_metta::parser::{parse_forms, TopForm};
use mork_metta::space::{LocalSpace, Pattern, Space};

// ========================================================================
// Fib tests  (from PeTTa's fib.metta)
// ========================================================================

#[test]
fn test_fib_30() {
    let mut rt = Runtime::new();
    let code = r#"
(= (fib $N)
   (if (< $N 2)
       $N
       (+ (fib (- $N 1))
          (fib (- $N 2)))))
!(test (fib 30) 832040)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

#[test]
fn test_fib_small_values() {
    let cases = [(0, "0"), (1, "1"), (2, "1"), (5, "5"), (10, "55")];
    for (n, expected) in cases {
        let mut rt = Runtime::new();
        let code = format!(
            r#"
(= (fib $N)
   (if (< $N 2)
       $N
       (+ (fib (- $N 1))
          (fib (- $N 2)))))
!(fib {})
"#,
            n
        );
        let result = rt.eval_str(&code).unwrap();
        assert_eq!(result.unwrap().to_sexpr_string(), expected, "fib({})", n);
    }
}

// ========================================================================
// Parse / compile
// ========================================================================

#[test]
fn test_parse_basic() {
    let forms = parse_forms("(= (f $x) $x)\n!(f 42)").unwrap();
    assert_eq!(forms.len(), 2);
}

#[test]
fn test_compile_basic() {
    let forms = parse_forms("(= (f $x) (+ $x 1))").unwrap();
    match &forms[0] {
        TopForm::Definition(expr) => {
            let (name, clause) = compile_definition(expr).unwrap();
            assert_eq!(name, "f");
            assert_eq!(clause.patterns.len(), 1);
            // First pattern should be $x
            if let mork_metta::parser::Expr::Symbol(s) = &clause.patterns[0] {
                assert_eq!(s, "$x");
            } else {
                panic!("expected Symbol pattern");
            }
        }
        _ => panic!("expected definition"),
    }
}

// ========================================================================
// Core eval (NDet API)
// ========================================================================

#[test]
fn test_eval_addition() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    let forms = parse_forms("!(+ 2 3)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let mut results = eval(&expr, &Env::new(), &funcs).unwrap();
    assert_eq!(results.next(), Some(Atom::Num(5)));
    assert_eq!(results.next(), None);
}

#[test]
fn test_unbound_variable_error() {
    // In MeTTa, $var self-evaluates to the variable atom. The error comes from
    // the numeric operator receiving a non-number, not from "unbound variable".
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    let forms = parse_forms("!(+ $x 1)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let result = eval(&expr, &Env::new(), &funcs);
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert!(err.contains("expected number"), "error: {}", err);
}

#[test]
fn test_unknown_symbol_as_data_list() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    // (foo 1 2 3) where foo is not a function -> data list (single Expr atom)
    let forms = parse_forms("!(foo 1 2 3)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let results: Vec<Atom> = eval(&expr, &Env::new(), &funcs).unwrap().collect();
    assert_eq!(results.len(), 1);
    assert_eq!(
        results[0],
        Atom::expr(vec![Atom::sym("foo"), Atom::Num(1), Atom::Num(2), Atom::Num(3)])
    );
}

#[test]
fn test_empty_list_is_value() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    // () should evaluate to the empty list value, not empty NDet
    let forms = parse_forms("!()").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let mut results = eval(&expr, &Env::new(), &funcs).unwrap();
    assert_eq!(results.next(), Some(Atom::expr(vec![])));
    assert_eq!(results.next(), None);
}

// ========================================================================
// Space storage
// ========================================================================

#[test]
fn test_space_stores_function_definitions() {
    let mut rt = Runtime::new();
    rt.eval_str("(= (f $x) (+ $x 1))").unwrap();
    let pat = Pattern::Expr(vec![
        Pattern::Exact(Atom::sym("=")),
        Pattern::Expr(vec![Pattern::Exact(Atom::sym("f")), Pattern::Any]),
        Pattern::Any,
    ]);
    let results = rt.funcs.space.lock().unwrap().match_atoms(&pat);
    assert_eq!(results.len(), 1);
}

#[test]
fn test_reify_functions_from_space() {
    let mut rt = Runtime::with_space(Box::new(LocalSpace::new()));
    let def_atom = Atom::Expr(vec![
        Atom::sym("="),
        Atom::Expr(vec![Atom::sym("g"), Atom::sym("$x")]),
        Atom::Expr(vec![Atom::sym("+"), Atom::sym("$x"), Atom::Num(3)]),
    ]);
    rt.funcs.space.lock().unwrap().add_atom(&def_atom).unwrap();
    rt.reify_functions();
    let forms = parse_forms("!(g 5)").unwrap();
    let result = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => {
            let mut results = eval(&e, &Env::new(), &rt.funcs).unwrap();
            results.next()
        }
        _ => panic!("expected runnable"),
    };
    assert_eq!(result, Some(Atom::Num(8)));
}

#[test]
fn test_local_space_basic() {
    let mut space = LocalSpace::new();
    space.add_atom(&Atom::expr(vec![Atom::sym("foo"), Atom::Num(1)])).unwrap();
    space.add_atom(&Atom::expr(vec![Atom::sym("foo"), Atom::Num(2)])).unwrap();
    space.add_atom(&Atom::expr(vec![Atom::sym("bar"), Atom::Num(3)])).unwrap();
    let pat = Pattern::Expr(vec![Pattern::Exact(Atom::sym("foo")), Pattern::Any]);
    let results = space.match_atoms(&pat);
    assert_eq!(results.len(), 2);
    let all = space.get_atoms();
    assert_eq!(all.len(), 3);
}

// ========================================================================
// progn
// ========================================================================

#[test]
fn test_progn_returns_last() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(progn (+ 1 2) (+ 3 4))").unwrap();
    assert_eq!(result, Some(Atom::Num(7)));
}

#[test]
fn test_progn_single_form() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(progn (+ 1 2))").unwrap();
    assert_eq!(result, Some(Atom::Num(3)));
}

#[test]
fn test_progn_empty_error() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    let forms = parse_forms("!(progn)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let result = eval(&expr, &Env::new(), &funcs);
    assert!(result.is_err());
}

// ========================================================================
// let
// ========================================================================

#[test]
fn test_let_basic() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let $x 5 (+ $x 3))").unwrap();
    assert_eq!(result, Some(Atom::Num(8)));
}

#[test]
fn test_let_shadowing() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let $x 1 (let $x 10 (+ $x 2)))").unwrap();
    assert_eq!(result, Some(Atom::Num(12)));
}

#[test]
fn test_let_pattern_no_match() {
    // Pattern-matching let: when pattern doesn't match value, produces empty stream
    let mut rt = Runtime::new();
    // (let 42 99 'ok) — pattern 42 vs value 99 → no match → empty
    let code = r#"!(collapse (let 42 99 'ok))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::expr(vec![])));
}
#[test]
fn test_let_pattern_literal() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let 42 42 (quote ok))").unwrap();
}
#[test]
fn test_let_pattern_destructure() {
    let mut rt = Runtime::new();
    let code = r#"!(let ($a $b) (superpose ((10 20))) (+ $a $b))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(30)));
}
#[test]
fn test_let_star_pattern_destructure() {
    let mut rt = Runtime::new();
    let code = r#"!(let* ((($x $y) (1 2))) (+ $x $y))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(3)));
}

#[test]
fn test_let_with_nondet() {
    let mut rt = Runtime::new();
    // superpose gets a single list arg -> branches for each element
    let code = r#"!(collapse (let $x (superpose (10 20 30)) (+ $x 1)))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(
        result,
        Some(Atom::expr(vec![Atom::Num(11), Atom::Num(21), Atom::Num(31)]))
    );
}

#[test]
fn test_let_inside_function() {
    let mut rt = Runtime::new();
    let code = r#"
(= (add5 $x) (let $y (+ $x 5) $y))
!(test (add5 10) 15)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

// ========================================================================
// let*
// ========================================================================

#[test]
fn test_let_star_basic() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let* (($x 1) ($y 2)) (+ $x $y))").unwrap();
    assert_eq!(result, Some(Atom::Num(3)));
}

#[test]
fn test_let_star_sequential() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let* (($x 3) ($y (* $x 2))) (+ $x $y))").unwrap();
    assert_eq!(result, Some(Atom::Num(9)));
}

#[test]
fn test_let_star_body_nondet() {
    let mut rt = Runtime::new();
    // superpose with single list arg containing expressions
    let code = r#"!(collapse (let* (($x 10)) (superpose ($x (+ $x 1) (+ $x 2)))))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(
        result,
        Some(Atom::expr(vec![Atom::Num(10), Atom::Num(11), Atom::Num(12)]))
    );
}

// ========================================================================
// quote
// ========================================================================

#[test]
fn test_quote_basic() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(quote (+ 1 2))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::sym("+"), Atom::Num(1), Atom::Num(2)])));
}

#[test]
fn test_quote_number() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(quote 42)").unwrap();
    assert_eq!(result, Some(Atom::Num(42)));
}

#[test]
fn test_quote_symbol() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(quote hello)").unwrap();
    assert_eq!(result, Some(Atom::sym("hello")));
}

#[test]
fn test_quote_nested() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(quote (a (b c) d))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![
        Atom::sym("a"),
        Atom::expr(vec![Atom::sym("b"), Atom::sym("c")]),
        Atom::sym("d"),
    ])));
}

// ========================================================================
// eval
// ========================================================================

#[test]
fn test_eval_quoted() {
    // PeTTa: (eval (quote (+ 1 2))) returns the quoted form as data, not 3.
    // eval([quote,[+,1,2]], Out) → translate quote → Out = [+,1,2].
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(eval (quote (+ 1 2)))").unwrap();
    assert_eq!(
        result,
        Some(Atom::expr(vec![Atom::sym("+"), Atom::Num(1), Atom::Num(2)]))
    );
}

#[test]
fn test_eval_number() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(eval 42)").unwrap();
    assert_eq!(result, Some(Atom::Num(42)));
}

#[test]
fn test_eval_quoted_variable() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(let $x 10 (eval (quote $x)))").unwrap();
    assert_eq!(result, Some(Atom::Num(10)));
}

#[test]
fn test_eval_with_user_function() {
    // PeTTa: (eval (quote (double 10))) returns (double 10) as data.
    // To evaluate stored code, use (eval $code) — the $var path re-evaluates the atom.
    let mut rt = Runtime::new();
    let code = r#"
(= (double $x) (* $x 2))
!(let $code (quote (double 10)) (eval $code))
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(20)));
}

#[test]
fn test_eval_empty_list() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(eval (quote ()))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![])));
}

// ========================================================================
// superpose + collapse  (PeTTa semantics: single list arg, Expr-unpack)
// ========================================================================

#[test]
fn test_superpose_basic() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(collapse (superpose (10 20 30)))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(10), Atom::Num(20), Atom::Num(30)])));
}

#[test]
fn test_superpose_single_element() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(collapse (superpose (42)))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(42)])));
}

#[test]
fn test_superpose_empty_list() {
    let mut rt = Runtime::new();
    // () evaluates to Expr([]), superpose has 0 literal elements → nothing
    let result = rt.eval_str("!(collapse (superpose ()))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![])));
}

#[test]
fn test_superpose_no_args_error() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    let forms = parse_forms("!(superpose)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let result = eval(&expr, &Env::new(), &funcs);
    assert!(result.is_err());
}

#[test]
fn test_superpose_multi_args_error() {
    let mut funcs = FnTable::new();
    register_builtins(&mut funcs);
    let forms = parse_forms("!(superpose 1 2 3)").unwrap();
    let expr = match forms.into_iter().next().unwrap() {
        TopForm::Runnable(e) => e,
        _ => panic!("expected runnable"),
    };
    let result = eval(&expr, &Env::new(), &funcs);
    assert!(result.is_err());
}

#[test]
fn test_superpose_with_expressions() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(collapse (superpose ((+ 1 2) (* 3 4))))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(3), Atom::Num(12)])));
}

#[test]
fn test_superpose_variable_list() {
    let mut rt = Runtime::new();
    // Bind a list to a variable, superpose unpacks it
    let code = r#"
(= (nums) (collapse (superpose (1 2 3))))
!(let $xs (nums) (collapse (superpose $xs)))
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(1), Atom::Num(2), Atom::Num(3)])));
}

#[test]
fn test_collapse_empty() {
    let mut rt = Runtime::new();
    // () is now the empty list value; progn returns it; collapse collects to [[]]
    let result = rt.eval_str("!(collapse (progn ()))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::expr(vec![])])));
}

// ========================================================================
// PeTTa example: collapse.metta
// ========================================================================

#[test]
fn test_collapse_data_list() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(test (collapse (1 2 3)) ((1 2 3)))").unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

// ========================================================================
// PeTTa example: identity.metta
// ========================================================================

#[test]
fn test_identity_example() {
    let mut rt = Runtime::new();
    let code = r#"
(= (f $x) (* $x $x))
!(test (f 1) 1)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

// ========================================================================
// PeTTa example: letstar.metta
// ========================================================================

#[test]
fn test_letstar_example() {
    let mut rt = Runtime::new();
    let code = "!(test (let* (($x 1) ($y 2)) (+ $x $y)) 3)";
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

// ========================================================================
// Combined: let + superpose (inspired by PeTTa's let_superpose_if_case)
// ========================================================================

#[test]
fn test_let_superpose_if() {
    let mut rt = Runtime::new();
    let code = r#"
!(collapse (let $y (superpose (2 3 4 5))
               (if (> $y 2) $y 99)))
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(99), Atom::Num(3), Atom::Num(4), Atom::Num(5)])));
}

// ========================================================================
// Arithmetic extras
// ========================================================================

#[test]
fn test_access_arithmetic() {
    let mut rt = Runtime::new();
    assert_eq!(rt.eval_str("!(/ 10 2)").unwrap(), Some(Atom::Num(5)));
    assert_eq!(rt.eval_str("!(* 3 4)").unwrap(), Some(Atom::Num(12)));
    assert_eq!(rt.eval_str("!(> 5 3)").unwrap(), Some(Atom::sym("True")));
    assert_eq!(rt.eval_str("!(== 5 5)").unwrap(), Some(Atom::sym("True")));
}

// ========================================================================
// quote tuple
// ========================================================================

#[test]
fn test_quote_tuple() {
    let mut rt = Runtime::new();
    // (quote (1 2 3)) returns the list as data
    let result = rt.eval_str("!(quote (1 2 3))").unwrap();
    assert_eq!(result, Some(Atom::expr(vec![Atom::Num(1), Atom::Num(2), Atom::Num(3)])));
}

// ========================================================================
// test builtin
// ========================================================================

#[test]
fn test_test_builtin_passes() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(test (+ 1 2) 3)").unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

#[test]
fn test_test_builtin_fails() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(test (+ 1 2) 999)").unwrap();
    assert_eq!(result, Some(Atom::sym("False")));
}
// ========================================================================
// Multi-clause functions (pattern matching)
// ========================================================================
#[test]
fn test_multi_clause_all_var() {
    // Multiple clauses with same name produce nondeterministic stream
    let mut rt = Runtime::new();
    let code = r#"
(= (f) 2)
(= (f) 3)
!(collapse (f))
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result.unwrap().to_sexpr_string(), "(2 3)");
}
#[test]
#[test]
fn test_multi_clause_literal_numbers() {
    // Clauses with literal number patterns — must NOT overlap with $var clause
    // (all matching clauses contribute, so guards on $var needed to exclude
    // values already matched by literals; without guards, $var matches everything)
    let mut rt = Runtime::new();
    let code = r#"
(= (fizzbuzz 3) "Fizz")
(= (fizzbuzz 5) "Buzz")
(= (fizzbuzz 15) "FizzBuzz")
(= (fizzbuzz $x) $x)
!(collapse (fizzbuzz 3))
"#;
    // (fizzbuzz 3) matches clause 1 ("Fizz") AND clause 4 ($x matches 3)
    let result = rt.eval_str(code).unwrap();
    let vals = result.unwrap();
    let s = vals.to_sexpr_string();
    assert!(s.contains("Fizz"), "expected Fizz in result, got {}", s);
}
fn test_multi_clause_literal_symbols() {
    let mut rt = Runtime::new();
    let code = r#"
(= (describe apple) red-fruit)
(= (describe banana) yellow-fruit)
(= (describe $x) unknown)
!(test (describe apple) red-fruit)
!(test (describe banana) yellow-fruit)
!(test (describe chair) unknown)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}
#[test]
fn test_multi_clause_no_match_error() {
    let mut rt = Runtime::new();
    let code = r#"
(= (g 1) 2)
(= (g 2) 3)
!(g 999)
"#;
    let result = rt.eval_str(code);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("no matching clause"));
}
#[test]
fn test_multi_clause_fallback_catches_all() {
    // When multiple clauses match (including a fallback $var),
    // ALL matching clauses contribute to the stream
    let mut rt = Runtime::new();
    let code = r#"
(= (pos 1) "one")
(= (pos 2) "two")
(= (pos 3) "three")
(= (pos $X) "many")
!(collapse (pos 1))
"#;
    // pos(1) matches clause 1 ("one") AND clause 4 ($X), so result is (one many)
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result.unwrap().to_sexpr_string(), "(one many)");
}
#[test]
fn test_multi_clause_structured_patterns() {
    // Destructuring patterns with nested lists
    let mut rt = Runtime::new();
    let code = r#"
(= (fst ($A $B)) $A)
!(test (fst (1 2)) 1)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

// ========================================================================
// foldall
// ========================================================================

#[test]
fn test_foldall_basic() {
    // foldall over a multi-clause generator with a named aggregate function
    let mut rt = Runtime::new();
    let code = r#"
(= (f) 2)
(= (f) 3)
(= (merge $A $B) (+ $A $B))
!(test (foldall merge (f) 0) 5)
"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

#[test]
fn test_foldall_single_value() {
    let mut rt = Runtime::new();
    let code = r#"!(foldall + (superpose (42)) 0)"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(42)));
}

#[test]
fn test_foldall_empty_generator() {
    let mut rt = Runtime::new();
    let code = r#"!(foldall + (superpose ()) 100)"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(100)));
}

#[test]
fn test_foldall_error_wrong_args() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(foldall + (f))");
    assert!(result.is_err());
}

// ========================================================================
// chain
// ========================================================================

#[test]
fn test_chain_basic() {
    let mut rt = Runtime::new();
    let code = r#"!(test (chain (+ 2 4) $n (* 3 $n)) 18)"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

#[test]
fn test_chain_nested() {
    let mut rt = Runtime::new();
    let code = r#"!(test (chain (+ 1 3) $n (chain (* 2 $n) $m (+ $n $m))) 12)"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}

#[test]
fn test_chain_single_expr() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(chain 42)").unwrap();
    assert_eq!(result, Some(Atom::Num(42)));
}

#[test]
fn test_chain_error_even_args() {
    let mut rt = Runtime::new();
    let result = rt.eval_str("!(chain 42 $n 99 $m)");
    assert!(result.is_err());
}

// ========================================================================
// case
// ========================================================================

#[test]
fn test_case_basic() {
    let mut rt = Runtime::new();
    let code = r#"!(case (quote (1 2)) ((($a $b) (+ $a $b))))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::Num(3)));
}

#[test]
fn test_case_catch_all() {
    let mut rt = Runtime::new();
    let code = r#"!(case 42 (($else (quote nothing))))"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("nothing")));
}

#[test]
fn test_case_no_match_error() {
    let mut rt = Runtime::new();
    let code = r#"!(case 99 ((1 a) (2 b)))"#;
    let result = rt.eval_str(code);
    assert!(result.is_err());
}

#[test]
fn test_case_multiple_clauses() {
    let mut rt = Runtime::new();
    let code = r#"!(test (case 2 ((1 (quote one)) (2 (quote two)) (3 (quote three)))) two)"#;
    let result = rt.eval_str(code).unwrap();
    assert_eq!(result, Some(Atom::sym("true")));
}
#[test]
fn test_multi_clause_compile() {
    // Test that compile_definition produces patterns correctly for literals
    use mork_metta::compile::compile_definition;
    use mork_metta::parser::{parse_forms, TopForm};
    let forms = parse_forms("(= (fib 0) 1)").unwrap();
    match &forms[0] {
        TopForm::Definition(expr) => {
            let (name, clause) = compile_definition(expr).unwrap();
            assert_eq!(name, "fib");
            assert_eq!(clause.patterns.len(), 1);
            // pattern should be Number(0), not a $var
            assert!(matches!(&clause.patterns[0], mork_metta::parser::Expr::Number(0)));
        }
        _ => panic!("expected definition"),
    }
}
