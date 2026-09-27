use deppy_python::{check_module, Target};

const SOURCE: &str = include_str!("../examples/proof_case/cantor.py");

#[test]
fn cantor_diagonal_proof_is_axiom_free() {
    let checked = check_module(SOURCE, Target::Python314).unwrap();
    assert!(checked.interface.exports().contains_key("cantor"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn cantor_requires_the_diagonal_negation() {
    let diagonal = "lambda x: negate(f(x)(x))";
    assert_eq!(SOURCE.matches(diagonal).count(), 1);
    let invalid = SOURCE.replace(diagonal, "lambda x: f(x)(x)");
    let error = check_module(&invalid, Target::Python314).err().unwrap();
    assert!(!error.message.contains("budget"), "{}", error.message);
}
