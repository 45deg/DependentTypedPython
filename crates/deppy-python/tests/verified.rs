use deppy_python::{analyze_module, check_module, Target};
const TARGET: Target = Target::Python314;
const HEADER: &str = r#"from __future__ import annotations
from deppy import dependent, axiom, Nat, Eq, refl, hole
from deppy.nat import add
from deppy.data import Bool, True_, False_, Unit, MkUnit
from deppy.verified import verified
"#;

#[test]
fn verified_examples_check_without_axioms_and_compute() {
    let source = format!(
        "{}{}",
        include_str!("../examples/verified.py")
            .replace("from deppy import Nat", "from deppy import dependent, Nat")
            .replace(
                "from deppy.data import Bool",
                "from deppy.data import Bool, True_, False_"
            ),
        r#"
@dependent
def computed() -> Eq[Nat, twice(3), 6]:
    return refl(6)
@dependent
def branch_true() -> Eq[Nat, choose(True_(), 5), 5]:
    return refl(5)
@dependent
def branch_false() -> Eq[Nat, choose(False_(), 7), 7]:
    return refl(7)
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn comparison_and_elif_denotations_compute() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(ensures=lambda a, b, result: Eq[Nat, result, 7], proof=lambda a, b, pre: hole("branches"))
def select(a: Nat, b: Nat) -> Nat:
    if a < b:
        x = 7
    elif b <= a:
        x = 7
    else:
        x = 7
    return x
"#
    );
    let analysis = analyze_module(&source, TARGET);
    assert!(!analysis.goals.is_empty());
    // Concrete conditions normalize, and different branch results are observed.
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(ensures=lambda result: Eq[Nat, result, 7], proof=lambda pre: refl(7))
def selected() -> Nat:
    if 1 < 0:
        x = 3
    elif 2 <= 2:
        x = 7
    else:
        x = 9
    return x
@dependent
def computed() -> Eq[Nat, selected(), 7]:
    return refl(7)
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn vc_goals_and_wrong_proofs_follow_the_current_body_and_contract() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(ensures=lambda n, result: Eq[Nat, result, add(n, n)], proof=lambda n, pre: refl(add(n, n)))
def twice(n: Nat) -> Nat:
    x = n
    x = x + n
    return x
"#
    );
    check_module(&source, TARGET).unwrap();
    for bad in [
        source.replace("return x", "return n"),
        source.replace("Eq[Nat, result, add(n, n)]", "Eq[Nat, result, 0]"),
        source.replace(
            "proof=lambda n, pre: refl(add(n, n))",
            "proof=lambda n, pre: refl(0)",
        ),
    ] {
        assert!(check_module(&bad, TARGET).is_err());
    }
    let analysis = analyze_module(
        &source.replace("refl(add(n, n))", "hole(\"twice_vc\")"),
        TARGET,
    );
    assert!(analysis.checked.is_none());
    assert!(analysis.goals.iter().any(|g| g.name == "twice_vc"));
}

#[test]
fn proof_axioms_are_not_hidden_by_unused_vc_let() {
    let source = format!(
        "{HEADER}{}",
        r#"
@axiom
def trust(n: Nat, pre: Unit) -> Eq[Nat, n, 0]:
    ...
@verified(ensures=lambda n, result: Eq[Nat, result, 0], proof=trust)
def identity(n: Nat) -> Nat:
    return n
"#
    );
    let checked = check_module(&source, TARGET).unwrap();
    assert_eq!(checked.axiom_dependencies["identity"], vec!["trust"]);
}

#[test]
fn unsupported_effects_and_invalid_local_states_are_rejected() {
    let prefix = format!("{HEADER}\n@verified(ensures=lambda flag, n, result: Unit, proof=lambda flag, n, pre: MkUnit())\ndef test(flag: Bool, n: Nat) -> Nat:\n");
    for body in [
        "    if flag:\n        x = n\n    return x\n",
        "    x = True\n    x = n\n    return x\n",
        "    x: Bool = n\n    return n\n",
        "    if n:\n        return n\n    return 0\n",
        "    while flag:\n        n = n + 1\n    return n\n",
        "    print(n)\n    return n\n",
        "    x = host(n)\n    return x\n",
        "    n = n - 1\n    return n\n",
        "    return n\n    while flag:\n        n = n + 1\n",
        "    if flag:\n        return n\n",
        "    x = n\n    x: Bool = True\n    return n\n",
    ] {
        assert!(
            check_module(&format!("{prefix}{body}"), TARGET).is_err(),
            "{body}"
        );
    }
}

#[test]
fn input_snapshot_and_bool_return_are_preserved() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(ensures=lambda n, result: Eq[Nat, result, add(n, 1)], proof=lambda n, pre: refl(add(n, 1)))
def increment(n: Nat) -> Nat:
    n = n + 1
    return n
@verified(ensures=lambda flag, result: Eq[Bool, result, flag], proof=lambda flag, pre: refl(flag))
def keep(flag: Bool) -> Bool:
    copy = flag
    flag = False
    return copy
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn pure_calls_use_the_current_state_and_validate_argument_types() {
    let source = format!(
        "{HEADER}{}",
        r#"
@dependent
def identity(n: Nat) -> Nat:
    return n
@dependent
def boolean(flag: Bool) -> Bool:
    return flag
@verified(ensures=lambda n, result: Eq[Nat, result, add(n, 2)], proof=lambda n, pre: refl(add(n, 2)))
def caller(n: Nat) -> Nat:
    n = identity(n + 2)
    flag: Bool = boolean(True)
    return n
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    for bad in [
        source.replace("identity(n + 2)", "identity(True)"),
        source.replace("boolean(True)", "boolean(n)"),
        source.replace("flag: Bool", "flag: Nat"),
    ] {
        assert!(check_module(&bad, TARGET).is_err());
    }
}

#[test]
fn malformed_contracts_and_decorators_cannot_bypass_verification() {
    for decorator in [
        "@verified",
        "@verified(ensures=lambda n, result: Unit)",
        "@verified(proof=lambda n, pre: MkUnit())",
        "@verified(ensures=lambda n, result: 0, proof=lambda n, pre: MkUnit())",
        "@verified(requires=lambda n: 0, ensures=lambda n, result: Unit, proof=lambda n, pre: MkUnit())",
        "@verified(ensures=lambda result: Unit, proof=lambda n, pre: MkUnit())",
        "@verified(ensures=lambda n, result: Unit, proof=lambda n: MkUnit())",
        "@verified(ensures=lambda n, result: Unit, proof=lambda n, pre: MkUnit(), trusted=True)",
    ] {
        let source = format!("{HEADER}\n{decorator}\ndef f(n: Nat) -> Nat:\n    return n\n");
        assert!(check_module(&source, TARGET).is_err(), "{decorator}");
    }
}

#[test]
fn imported_verified_declarations_are_checked_before_use() {
    let library = format!("{HEADER}\n@verified(ensures=lambda n, result: Eq[Nat, result, n], proof=lambda n, pre: refl(n))\ndef identity(n: Nat) -> Nat:\n    return n\n");
    let source = format!("{HEADER}\nfrom library import identity\n@dependent\ndef computed() -> Eq[Nat, identity(3), 3]:\n    return refl(3)\n");
    let mut resolver = |_: &str| Ok(Some(library.clone()));
    deppy_python::check_module_with_resolver(&source, TARGET, &mut resolver).unwrap();
    let mut resolver = |_: &str| Ok(Some(library.replace("return n", "return 0")));
    assert!(deppy_python::check_module_with_resolver(&source, TARGET, &mut resolver).is_err());
}
