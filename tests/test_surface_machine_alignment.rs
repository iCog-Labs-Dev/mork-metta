use mork_metta::atom::Atom;
use mork_metta::eval_parts::cek::{with_engine, Engine};
use mork_metta::space::Space;
use mork_metta::Runtime;

fn run_atom(rt: &mut Runtime, code: &str) -> Atom {
    rt.eval_str(code).unwrap().unwrap()
}

#[test]
fn test_surface_with_mutex_is_live_special_form() {
    let mut rt = Runtime::new();

    assert_eq!(
        run_atom(
            &mut rt,
            "!(with_mutex testmutex (add-atom &guarded (cnt 5)))"
        ),
        Atom::sym("true")
    );
    assert_eq!(
        run_atom(&mut rt, "!(match &guarded (cnt $x) $x)"),
        Atom::Num(5)
    );
}

#[test]
fn test_transaction_rolls_back_space_mutations() {
    let mut rt = Runtime::new();

    assert_eq!(
        run_atom(&mut rt, "!(add-atom &dfdf (cnt 42))"),
        Atom::sym("true")
    );
    assert_eq!(
        rt.eval_str(
            "!(transaction (match &dfdf (cnt $x) ((remove-atom &dfdf (cnt $x)) (let $inc (+ $x 1) (add-atom &dfdf (cnt $inc))) (empty))))"
        )
        .unwrap(),
        None
    );
    assert_eq!(
        run_atom(&mut rt, "!(match &dfdf (cnt $x) $x)"),
        Atom::Num(42)
    );
}

#[test]
fn test_surface_add_atom_dispatches_through_machine_side_effects() {
    let mut rt = Runtime::new();

    let added = rt
        .eval_str("!(add-atom &self (= (h $x) (+ $x 100)))")
        .unwrap();

    assert_eq!(added, Some(Atom::sym("true")));
    assert_eq!(run_atom(&mut rt, "!(h 5)"), Atom::Num(105));
}

#[test]
fn test_surface_remove_atom_clears_dispatch_and_shadow_head() {
    let mut rt = Runtime::new();
    rt.eval_str("!(add-atom &self (= (h $x) (+ $x 100)))")
        .unwrap();

    let removed = rt
        .eval_str("!(remove-atom &self (= (h $x) (+ $x 100)))")
        .unwrap();

    assert_eq!(removed, Some(Atom::sym("true")));
    assert_eq!(
        run_atom(&mut rt, "!(h 5)"),
        Atom::Expr(vec![Atom::sym("h"), Atom::Num(5)])
    );

    let shadow = Atom::Expr(vec![Atom::sym("h"), Atom::sym("$x")]);
    let atoms = rt.funcs.space.read().unwrap().get_atoms();
    assert!(!atoms.contains(&shadow));
}

#[test]
fn test_surface_transform_is_live_under_cek() {
    let mut rt = Runtime::new();
    rt.funcs
        .space
        .write()
        .unwrap()
        .add_atom(&Atom::sym("slow"))
        .unwrap();

    let top_level = with_engine(Engine::Cek, || rt.eval_str("!(transform slow fast)")).unwrap();
    assert_eq!(top_level, Some(Atom::sym("fast")));

    rt.eval_str("(= (rewrite) (transform slow fast))").unwrap();
    let nested = with_engine(Engine::Cek, || rt.eval_str("!(rewrite)")).unwrap();
    assert_eq!(nested, Some(Atom::sym("fast")));
}

#[test]
fn test_match_supports_comma_conjunction_patterns() {
    let mut rt = Runtime::new();
    rt.eval_str("!(add-atom &self (friend tim tom))").unwrap();
    rt.eval_str("!(add-atom &self (friend tom tam))").unwrap();
    rt.eval_str("!(add-atom &self (friend sim som))").unwrap();
    rt.eval_str("!(add-atom &self (friend som sam))").unwrap();

    assert_eq!(
        run_atom(
            &mut rt,
            "!(test (msort (collapse (match &self (, (friend $1 $2) (friend $2 $3)) ($1 $2 $3)))) ((sim som sam) (tim tom tam)))",
        ),
        Atom::sym("true")
    );
}

#[test]
fn test_named_spaces_are_isolated_from_self() {
    let mut rt = Runtime::new();

    assert_eq!(
        run_atom(&mut rt, "!(add-atom &self (cnt 1))"),
        Atom::sym("true")
    );
    assert_eq!(
        run_atom(&mut rt, "!(add-atom &dfdf (cnt 37))"),
        Atom::sym("true")
    );
    assert_eq!(
        run_atom(&mut rt, "!(match &self (cnt $x) $x)"),
        Atom::Num(1)
    );
    assert_eq!(
        run_atom(&mut rt, "!(match &dfdf (cnt $x) $x)"),
        Atom::Num(37)
    );
    assert_eq!(
        run_atom(&mut rt, "!(collapse (get-atoms &dfdf))"),
        Atom::Expr(vec![Atom::Expr(vec![Atom::sym("cnt"), Atom::Num(37)])])
    );

    assert_eq!(
        run_atom(&mut rt, "!(remove-atom &dfdf (cnt 37))"),
        Atom::sym("true")
    );
    assert_eq!(
        run_atom(&mut rt, "!(collapse (get-atoms &dfdf))"),
        Atom::Expr(vec![])
    );
    assert_eq!(
        run_atom(&mut rt, "!(match &self (cnt $x) $x)"),
        Atom::Num(1)
    );
}
