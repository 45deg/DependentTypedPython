use deppy_python::{analyze_module, check_module, Target};
const TARGET: Target = Target::Python314;
const HEADER: &str = r#"from __future__ import annotations
from deppy import dependent, theorem, Nat, S, Eq, refl, hole
from deppy.data import Bool, True_, False_, Unit, MkUnit
from deppy.nat import add
from deppy.verified import verified, Refined, verified_spec
"#;

#[test]
fn refined_returns_preserve_base_values_and_entry_arguments() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(proof=lambda n, pre: refl(S(n)))
def increment(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, S(n)]]:
    n = S(n)
    return n
@theorem
def reuse(n: Nat) -> Eq[Nat, increment(n), S(n)]:
    return verified_spec(increment, n, MkUnit())
@dependent
def concrete() -> Eq[Nat, increment(2), 3]:
    return refl(3)
@verified(proof=lambda flag, pre: refl(flag))
def keep(flag: Bool) -> Refined[Bool, lambda result: Eq[Bool, result, flag]]:
    old = flag
    flag = False
    return old
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    assert!(checked.interface.exports()["increment"]
        .verified_spec
        .is_some());
    check_module(
        &source.replace("Refined", "RefinedAlias").replace(
            "import verified, RefinedAlias",
            "import verified, Refined as RefinedAlias",
        ),
        TARGET,
    )
    .unwrap();
}

#[test]
fn refinement_predicate_binder_shadows_input_and_requires_is_preserved() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(requires=lambda n: Eq[Nat, n, 0], proof=lambda n, pre: pre)
def zero(n: Nat) -> Refined[Nat, lambda n: Eq[Nat, n, 0]]:
    return n
@theorem
def use(n: Nat, pre: Eq[Nat, n, 0]) -> Eq[Nat, zero(n), 0]:
    return verified_spec(zero, n, pre)
"#
    );
    check_module(&source, TARGET).unwrap();
    assert!(check_module(
        &source.replace(
            "verified_spec(zero, n, pre)",
            "verified_spec(zero, n, MkUnit())"
        ),
        TARGET
    )
    .is_err());
}

#[test]
fn malformed_refinements_and_false_proofs_are_rejected() {
    let source = format!("{HEADER}\n@verified(proof=lambda n, pre: refl(n))\ndef identity(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, n]]:\n    return n\n");
    for bad in [
        source.replace("return n", "return S(n)"),
        source.replace("result, n]", "result, S(n)]"),
        source.replace(
            "Refined[Nat, lambda result: Eq[Nat, result, n]]",
            "Refined[Nat, lambda result: 0]",
        ),
        source.replace("Refined[Nat,", "Refined[Bool,"),
        source.replace(
            "Refined[Nat, lambda result: Eq[Nat, result, n]]",
            "Refined[Nat]",
        ),
        source.replace(
            "Refined[Nat, lambda result: Eq[Nat, result, n]]",
            "Refined[Nat, lambda result: Unit, Nat]",
        ),
        source.replace("@verified(", "@verified(ensures=lambda n, result: Unit, "),
        source.replace(
            "    return n",
            "    x: Refined[Nat, lambda x: Unit] = n\n    return x",
        ),
    ] {
        assert!(check_module(&bad, TARGET).is_err(), "{bad}");
    }
    let analysis = analyze_module(
        &source.replace("refl(n)", "hole(\"return_refinement\")"),
        TARGET,
    );
    assert!(analysis.checked.is_none());
    assert!(analysis.goals.iter().any(|g| g.name == "return_refinement"));
}

#[test]
fn parallel_assignment_reads_every_rhs_before_updates() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(proof=lambda a, b, pre: refl(add(b, a)))
def swap(a: Nat, b: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, add(b, a)]]:
    a, b = b, a
    return a + b
@dependent
def concrete() -> Eq[Nat, swap(2, 5), 7]:
    return refl(7)
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    for assignment in [
        "a = b\n    b = a",
        "a, a = b, a",
        "a, b = b,",
        "a, b = b, True",
        "a, b = unknown, a",
        "a, (b, c) = b, a",
    ] {
        assert!(
            check_module(&source.replace("a, b = b, a", assignment), TARGET).is_err(),
            "{assignment}"
        );
    }
}

#[test]
fn fibonacci_proves_general_equality_and_concrete_results_without_axioms() {
    let mut source = include_str!("../examples/fibonacci.py").to_owned();
    for (n, expected) in [(0, 0), (1, 1), (2, 1), (3, 2)] {
        source.push_str(&format!("\n@dependent\ndef value_{n}() -> Eq[Nat, fib_loop({n}), {expected}]:\n    return refl({expected})\n"));
    }
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    for name in ["fib_loop", "fib_loop_correct", "fib_loop_twice"] {
        assert!(checked.axiom_dependencies.contains_key(name));
    }
}

#[test]
fn fibonacci_mutations_do_not_reuse_stale_proofs() {
    let source = include_str!("../examples/fibonacci.py");
    for (from, to) in [
        ("a, b = b, a + b", "a = b\n        b = a + b"),
        ("a, b = 0, 1", "a, b = 1, 1"),
        (
            "decreases(lambda remaining, index, a, b: remaining)",
            "decreases(lambda remaining, index, a, b: 0)",
        ),
        ("    return a", "    return b"),
    ] {
        assert!(
            check_module(&source.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}
