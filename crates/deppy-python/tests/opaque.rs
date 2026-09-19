use deppy_python::{check_module, check_module_with_resolver, Target};

#[test]
fn opaque_theorems_check_bodies_and_preserve_dependencies_across_imports() {
    let library = "from __future__ import annotations\nfrom deppy import dependent, axiom, Nat, Eq, refl\n@axiom\ndef assumption() -> Eq[Nat, 0, 0]:\n    ...\n@dependent(opaque=True)\ndef theorem() -> Eq[Nat, 0, 0]:\n    return assumption()\n";
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq\nfrom library import theorem\n@dependent\ndef use() -> Eq[Nat, 0, 0]:\n    return theorem()\n";
    let mut resolver = |name: &str| Ok((name == "library").then(|| library.to_owned()));
    let module = check_module_with_resolver(source, Target::Python314, &mut resolver).unwrap();
    assert_eq!(module.axiom_dependencies["use"], vec!["library.assumption"]);
    let id = module
        .definitions
        .iter()
        .find(|(name, _, _)| name == "use")
        .unwrap()
        .1;
    assert!(matches!(
        module
            .elaborator
            .kernel()
            .normalize(&deppy_core::Term::Global(id).arc())
            .unwrap()
            .as_ref(),
        deppy_core::Term::Global(_)
    ));
    assert!(check_module(
        &library.replace("return assumption()", "return 0"),
        Target::Python314
    )
    .is_err());
}

#[test]
fn opaque_values_do_not_unfold_during_elaboration() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\n@dependent(opaque=True)\ndef hidden() -> Nat:\n    return 0\n@dependent\ndef wrong() -> Eq[Nat, hidden(), 0]:\n    return refl(0)\n";
    assert!(check_module(source, Target::Python314).is_err());
    assert!(check_module(
        &source.replace("opaque=True", "opaque=False"),
        Target::Python314
    )
    .is_ok());
    assert!(check_module(
        &source.replace("opaque=True", "opaque=1"),
        Target::Python314
    )
    .is_err());
    assert!(check_module(
        &source.replace("opaque=True", "opaque=True, opaque=False"),
        Target::Python314
    )
    .is_err());
}

#[test]
fn checked_interface_retains_the_exact_environment_and_declaration_kind() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent(opaque=True)\ndef theorem() -> Nat:\n    return 0\n";
    let mut module = check_module(source, Target::Python314).unwrap();
    let entry = &module.interface.exports()["theorem"];
    assert_eq!(entry.kind, deppy_python::DeclarationKind::Opaque);
    module
        .interface
        .kernel()
        .check(&deppy_core::Term::Global(entry.id).arc(), &entry.ty)
        .unwrap();
    let id = module
        .elaborator
        .define(
            "later",
            Some(&deppy_elab::Expr::Nat),
            &deppy_elab::Expr::Zero,
        )
        .unwrap();
    assert!(module.interface.kernel().definition(id).is_err());
    assert!(!module.interface.exports().contains_key("later"));
}

#[test]
fn diamond_imports_share_opaque_declaration_identity() {
    let common = "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent(opaque=True)\ndef hidden() -> Nat:\n    return 0\n";
    let bridge = "from common import hidden\n";
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\nfrom left import hidden as a\nfrom right import hidden as b\n@dependent\ndef same() -> Eq[Nat, a(), b()]:\n    return refl(a())\n";
    let mut common_loads = 0;
    let mut resolver = |name: &str| {
        Ok(match name {
            "common" => {
                common_loads += 1;
                Some(common.to_owned())
            }
            "left" | "right" => Some(bridge.to_owned()),
            _ => None,
        })
    };
    let module = check_module_with_resolver(source, Target::Python314, &mut resolver).unwrap();
    assert_eq!(common_loads, 1);
    assert!(module.interface.exports()["same"]
        .axiom_dependencies
        .is_empty());
}
