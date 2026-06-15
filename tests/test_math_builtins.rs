use mork_metta::atom::Atom;
use mork_metta::Runtime;

fn run_atom(rt: &mut Runtime, code: &str) -> Atom {
    rt.eval_str(code).unwrap().unwrap()
}

#[test]
fn test_float_math_preserves_decimal_forms() {
    let mut rt = Runtime::new();

    assert_eq!(run_atom(&mut rt, "!(sqrt-math 9)"), Atom::sym("3.0"));
    assert_eq!(run_atom(&mut rt, "!(sin-math 0)"), Atom::sym("0.0"));
    assert_eq!(run_atom(&mut rt, "!(cos-math 0)"), Atom::sym("1.0"));
}

#[test]
fn test_log_math_uses_first_arg_as_base() {
    let mut rt = Runtime::new();

    assert_eq!(run_atom(&mut rt, "!(log-math 10 100)"), Atom::sym("2.0"));
}
