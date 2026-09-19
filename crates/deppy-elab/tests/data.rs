use deppy_elab::{Elaborator, Expr as E, NamedConstructor, NamedDataDecl, Plicity};

fn list() -> NamedDataDecl {
    NamedDataDecl {
        name: "List".into(),
        parameters: vec![("A".into(), E::Universe(0))],
        indices: vec![],
        level: 0,
        constructors: vec![
            NamedConstructor {
                name: "Nil".into(),
                fields: vec![],
                result: E::name("List").implicit(E::name("A")),
            },
            NamedConstructor {
                name: "Cons".into(),
                fields: vec![
                    ("head".into(), E::name("A")),
                    ("tail".into(), E::name("List").implicit(E::name("A"))),
                ],
                result: E::name("List").implicit(E::name("A")),
            },
        ],
    }
}
#[test]
fn failed_constructor_registration_leaves_family_and_names_available() {
    let mut elab = Elaborator::default();
    let mut invalid = list();
    invalid.constructors[1].fields[1].1 = E::pi(
        "bad",
        Plicity::Explicit,
        E::name("List").implicit(E::name("A")),
        E::Nat,
    );
    assert!(elab.declare_data(7, invalid).is_err());
    assert!(elab.kernel().data_declaration(7).is_err());
    for name in ["List", "Nil", "Cons"] {
        assert!(elab.infer(&E::name(name)).is_err());
    }
    let exports = elab.declare_data(7, list()).unwrap();
    assert_eq!(exports.len(), 3);
    assert!(elab.infer(&E::name("Nil").implicit(E::Nat)).is_ok());
}
#[test]
fn constructor_result_must_use_the_same_family_and_uniform_parameters() {
    for result in [E::Nat, E::name("List").implicit(E::Nat)] {
        let mut elab = Elaborator::default();
        let mut invalid = list();
        invalid.constructors[0].result = result;
        assert!(elab.declare_data(0, invalid).is_err());
        assert!(elab.infer(&E::name("List")).is_err());
    }
}
