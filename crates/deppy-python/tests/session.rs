use deppy_python::{CheckSession, FrontendOptions};

#[test]
fn checked_dependencies_are_reused_and_changes_invalidate_the_snapshot() {
    let mut session = CheckSession::default();
    let mut library = "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent\ndef number() -> Nat:\n    return 2\n".to_owned();
    let root = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\nfrom library import number\n@dependent\ndef proof() -> Eq[Nat, number(), 2]:\n    return refl(2)\n";
    let options = FrontendOptions::default();
    session
        .check(root, options, &mut |_: &str| Ok(Some(library.clone())))
        .unwrap();
    assert_eq!(session.reused_declarations(), 0);
    session
        .check(root, options, &mut |_: &str| Ok(Some(library.clone())))
        .unwrap();
    assert!(session.reused_declarations() > 0);
    library = library.replace("return 2", "return 3");
    assert!(session
        .check(root, options, &mut |_: &str| Ok(Some(library.clone())))
        .is_err());
    assert_eq!(session.reused_declarations(), 0);
    let changed = root.replace(", 2]", ", 3]").replace("refl(2)", "refl(3)");
    session
        .check(&changed, options, &mut |_: &str| Ok(Some(library.clone())))
        .unwrap();
    assert_eq!(session.reused_declarations(), 0);
    session
        .check(&changed, options, &mut |_: &str| Ok(Some(library.clone())))
        .unwrap();
    assert!(session.reused_declarations() > 0);
}

#[test]
fn snapshots_keep_inductive_and_record_identity_and_private_helpers() {
    let mut session = CheckSession::default();
    let library = "from __future__ import annotations\nfrom deppy import inductive, constructor, record, dependent, Type, Nat\n@inductive\nclass Box[A: Type]:\n    @constructor\n    def Mk(value: A) -> Box[A]: ...\n@record\nclass Pair:\n    left: Nat\n    right: Nat\n@dependent\ndef box() -> Box[Nat]:\n    return Mk(7)\n";
    let root = "from __future__ import annotations\nfrom deppy import dependent, Nat\nfrom library import Box, Mk, Pair, box\n@dependent\ndef read() -> Nat:\n    value = Pair(1, 2)\n    return value.right\n@dependent\ndef same() -> Box[Nat]:\n    return box()\n";
    for _ in 0..2 {
        let checked = session
            .check(root, FrontendOptions::default(), &mut |_: &str| {
                Ok(Some(library.to_owned()))
            })
            .unwrap();
        let exports = checked.interface.exports();
        assert_eq!(
            exports["Box"].kind,
            deppy_python::DeclarationKind::Inductive
        );
        assert_eq!(
            exports["Mk"].kind,
            deppy_python::DeclarationKind::Constructor
        );
        assert_eq!(exports["Pair"].projections.len(), 2);
        checked
            .interface
            .kernel()
            .infer(&exports["Pair"].projections["right"])
            .unwrap();
    }
    assert!(session.reused_declarations() >= 3);
    let failed = root.replace("return value.right", "return unknown");
    assert!(session
        .check(&failed, FrontendOptions::default(), &mut |_: &str| Ok(
            Some(library.to_owned())
        ))
        .is_err());
    session
        .check(root, FrontendOptions::default(), &mut |_: &str| {
            Ok(Some(library.to_owned()))
        })
        .unwrap();
    assert!(session.reused_declarations() >= 3);
}
