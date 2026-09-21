use deppy_core::Transparency;
use deppy_python::{
    check_module, check_module_with_resolver, CheckSession, FrontendOptions, Target,
};
const TARGET: Target = Target::Python314;
const HEADER: &str = r#"from __future__ import annotations
from deppy import dependent, theorem, axiom, Nat, S, Eq, refl
from deppy.data import Unit, MkUnit
from deppy.nat import add
from deppy.verified import verified, verified_spec
"#;
fn library() -> String {
    format!("{HEADER}\n@verified(ensures=lambda n, result: Eq[Nat, result, n], proof=lambda n, pre: refl(n))\ndef identity(n: Nat) -> Nat:\n    return n\n")
}

#[test]
fn local_specification_is_an_opaque_checked_theorem() {
    let source = format!(
        "{}{}",
        library(),
        r#"
@theorem
def reused(n: Nat) -> Eq[Nat, identity(n), n]:
    return verified_spec(identity, n, MkUnit())
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    let entry = &checked.interface.exports()["identity"];
    let spec = checked
        .interface
        .kernel()
        .definition(entry.verified_spec.unwrap())
        .unwrap();
    assert!(spec.body.is_some());
    assert_eq!(spec.transparency, Transparency::Opaque);
    assert!(checked.interface.exports()["reused"]
        .verified_spec
        .is_none());
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn alias_and_reexport_preserve_the_specification_binding() {
    let source = format!("{HEADER}\nfrom facade import renamed\n@theorem\ndef reuse(n: Nat) -> Eq[Nat, renamed(n), n]:\n    return verified_spec(renamed, n, MkUnit())\n");
    let mut resolver = |name: &str| {
        Ok(match name {
            "library" => Some(library()),
            "facade" => Some(
                "from __future__ import annotations\nfrom library import identity as renamed\n"
                    .into(),
            ),
            _ => None,
        })
    };
    let checked = check_module_with_resolver(&source, TARGET, &mut resolver).unwrap();
    assert!(checked.axiom_dependencies["reuse"].is_empty());
    assert!(checked.interface.exports()["renamed"]
        .verified_spec
        .is_some());
}

#[test]
fn full_loop_specs_can_be_reused_for_symbolic_inputs() {
    let mut resolver = |name: &str| {
        Ok(match name {
            "verified" => Some(include_str!("../examples/verified.py").into()),
            "verified_loop" => Some(include_str!("../examples/verified_loop.py").into()),
            _ => None,
        })
    };
    let checked = check_module_with_resolver(
        include_str!("../examples/verified_spec.py"),
        TARGET,
        &mut resolver,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn preconditions_and_verified_provenance_are_required() {
    let prefix = format!(
        "{HEADER}{}",
        r#"
@verified(requires=lambda n: Eq[Nat, n, 0], ensures=lambda n, result: Eq[Nat, result, 0], proof=lambda n, pre: pre)
def restricted(n: Nat) -> Nat:
    return n
@dependent
def ordinary(n: Nat) -> Nat:
    return n
"#
    );
    for term in [
        "verified_spec(restricted, n, MkUnit())",
        "verified_spec(restricted, n)",
        "verified_spec(ordinary, n, refl(n))",
        "verified_spec(missing, n, refl(n))",
        "verified_spec(restricted(n), n, refl(n))",
        "verified_spec(restricted, n, refl(n), refl(n))",
        "verified_spec(restricted, n, pre=refl(n))",
    ] {
        let source =
            format!("{prefix}\n@theorem\ndef bad(n: Nat) -> Eq[Nat, n, 0]:\n    return {term}\n");
        assert!(check_module(&source, TARGET).is_err(), "{term}");
    }
    let shadowed = format!("{prefix}\n@theorem\ndef bad(restricted: Nat) -> Eq[Nat, restricted, 0]:\n    return verified_spec(restricted, restricted, refl(restricted))\n");
    assert!(check_module(&shadowed, TARGET).is_err());
}

#[test]
fn nullary_functions_and_builtin_aliases_work() {
    let source = format!(
        "{}{}",
        HEADER.replace("verified_spec", "verified_spec as spec"),
        r#"
@verified(ensures=lambda result: Eq[Nat, result, 3], proof=lambda pre: refl(3))
def three() -> Nat:
    return 3
@theorem
def reuse() -> Eq[Nat, three(), 3]:
    return spec(three, MkUnit())
"#
    );
    check_module(&source, TARGET).unwrap();
}

#[test]
fn axiom_dependencies_propagate_through_reused_specs() {
    let source = format!(
        "{HEADER}{}",
        r#"
@axiom
def trusted(n: Nat) -> Eq[Nat, n, 0]:
    ...
@verified(ensures=lambda n, result: Eq[Nat, result, 0], proof=lambda n, pre: trusted(n))
def identity(n: Nat) -> Nat:
    return n
@theorem
def reuse(n: Nat) -> Eq[Nat, identity(n), 0]:
    return verified_spec(identity, n, MkUnit())
"#
    );
    let checked = check_module(&source, TARGET).unwrap();
    assert_eq!(checked.axiom_dependencies["reuse"], vec!["trusted"]);
}

#[test]
fn dependency_changes_invalidate_the_companion_theorem() {
    let root = format!("{HEADER}\nfrom library import identity\n@theorem\ndef reuse(n: Nat) -> Eq[Nat, identity(n), n]:\n    return verified_spec(identity, n, MkUnit())\n");
    let mut session = CheckSession::default();
    let options = FrontendOptions::default();
    for _ in 0..2 {
        session
            .check(&root, options, &mut |_: &str| Ok(Some(library())))
            .unwrap();
    }
    assert!(session.reused_declarations() > 0);
    // The changed function and its new specification are valid together, but
    // the old client theorem no longer follows.
    let changed = library()
        .replace("result, n]", "result, S(n)]")
        .replace("refl(n)", "refl(S(n))")
        .replace("return n", "return S(n)");
    assert!(session
        .check(&root, options, &mut |_: &str| Ok(Some(changed.clone())))
        .is_err());
    assert_eq!(session.reused_declarations(), 0);
    let changed_pre =
        library().replace("@verified(", "@verified(requires=lambda n: Eq[Nat, n, 0], ");
    assert!(session
        .check(&root, options, &mut |_: &str| Ok(Some(changed_pre.clone())))
        .is_err());
}
