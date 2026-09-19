use deppy_core::{ConstructorDecl, DataDecl, DataOp, Error, Kernel, Relevance, Term, Tm};
fn v(n: usize) -> Tm {
    Term::Var(n).arc()
}
fn data(op: DataOp, arguments: Vec<Tm>) -> Tm {
    Term::Data { op, arguments }.arc()
}
fn nat() -> Tm {
    Term::Nat.arc()
}
fn zero() -> Tm {
    Term::Zero.arc()
}
fn pi(domain: Tm, codomain: Tm) -> Tm {
    Term::Pi {
        relevance: Relevance::Runtime,
        domain,
        codomain,
    }
    .arc()
}
fn lam(domain: Tm, body: Tm) -> Tm {
    Term::Lam {
        relevance: Relevance::Runtime,
        domain,
        body,
    }
    .arc()
}
fn family(id: u64) -> Tm {
    data(DataOp::Type(id), vec![])
}
fn naturals() -> DataDecl {
    DataDecl {
        parameters: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            ConstructorDecl {
                fields: vec![],
                indices: vec![],
            },
            ConstructorDecl {
                fields: vec![family(0)],
                indices: vec![],
            },
        ],
    }
}
#[test]
fn multiple_constructors_and_recursive_computation() {
    let mut k = Kernel::default();
    k.declare_data(0, naturals()).unwrap();
    let z = data(DataOp::Constructor(0, 0), vec![]);
    let s = data(DataOp::Constructor(0, 1), vec![z]);
    let term = data(
        DataOp::Eliminate(0, 0),
        vec![
            lam(family(0), nat()),
            zero(),
            lam(family(0), lam(nat(), Term::Succ(v(0)).arc())),
            s,
        ],
    );
    assert_eq!(k.normalize(&term).unwrap(), Term::Succ(zero()).arc());
}
#[test]
fn empty_elimination_is_neutral_and_requires_an_inhabitant() {
    let mut k = Kernel::default();
    k.declare_data(
        0,
        DataDecl {
            parameters: vec![],
            indices: vec![],
            constructors: vec![],
            level: 0,
        },
    )
    .unwrap();
    let body = data(DataOp::Eliminate(0, 0), vec![lam(family(0), nat()), v(0)]);
    k.infer(&lam(family(0), body)).unwrap();
    assert!(k.infer(&data(DataOp::Constructor(0, 0), vec![])).is_err());
    assert!(k
        .infer(&data(
            DataOp::Eliminate(0, 0),
            vec![lam(family(0), nat()), zero()]
        ))
        .is_err());
}
#[test]
fn negative_double_negative_and_nonuniform_recursion_are_rejected_atomically() {
    for field in [pi(family(0), nat()), pi(pi(family(0), nat()), nat())] {
        let mut k = Kernel::default();
        let mut d = naturals();
        d.constructors[1].fields = vec![field];
        assert_eq!(k.declare_data(0, d), Err(Error::InvalidPositivity));
        assert!(k.data_declaration(0).is_err());
        k.declare_data(0, naturals()).unwrap();
    }
    let mut k = Kernel::default();
    let d = DataDecl {
        parameters: vec![Term::Universe(0).arc()],
        indices: vec![],
        level: 0,
        constructors: vec![ConstructorDecl {
            fields: vec![data(DataOp::Type(0), vec![nat()])],
            indices: vec![],
        }],
    };
    assert_eq!(k.declare_data(0, d), Err(Error::InvalidPositivity));
}
#[test]
fn indexed_constructor_checks_and_refines_result() {
    let mut k = Kernel::default();
    k.declare_data(
        0,
        DataDecl {
            parameters: vec![Term::Universe(0).arc()],
            indices: vec![nat()],
            level: 0,
            constructors: vec![
                ConstructorDecl {
                    fields: vec![],
                    indices: vec![zero()],
                },
                ConstructorDecl {
                    fields: vec![nat(), v(1), data(DataOp::Type(0), vec![v(2), v(1)])],
                    indices: vec![Term::Succ(v(2)).arc()],
                },
            ],
        },
    )
    .unwrap();
    let nil = data(DataOp::Constructor(0, 0), vec![nat()]);
    let cons = data(
        DataOp::Constructor(0, 1),
        vec![nat(), zero(), zero(), nil.clone()],
    );
    assert_eq!(
        k.infer(&cons).unwrap(),
        data(DataOp::Type(0), vec![nat(), Term::Succ(zero()).arc()])
    );
    assert!(k
        .infer(&data(
            DataOp::Constructor(0, 1),
            vec![nat(), Term::Succ(zero()).arc(), zero(), nil]
        ))
        .is_err());
    let motive = lam(nat(), lam(data(DataOp::Type(0), vec![nat(), v(0)]), nat()));
    let step = lam(
        nat(),
        lam(
            nat(),
            lam(
                data(DataOp::Type(0), vec![nat(), v(1)]),
                lam(nat(), Term::Succ(v(0)).arc()),
            ),
        ),
    );
    let count = data(
        DataOp::Eliminate(0, 0),
        vec![nat(), Term::Succ(zero()).arc(), motive, zero(), step, cons],
    );
    assert_eq!(k.normalize(&count).unwrap(), Term::Succ(zero()).arc());
}
#[test]
fn positive_function_field_induction() {
    let mut k = Kernel::default();
    let mut d = naturals();
    d.constructors[1].fields = vec![pi(nat(), family(0))];
    k.declare_data(0, d).unwrap();
    let z = data(DataOp::Constructor(0, 0), vec![]);
    let node = data(DataOp::Constructor(0, 1), vec![lam(nat(), z)]);
    let at_zero = Term::App {
        function: v(0),
        argument: zero(),
    }
    .arc();
    let step = lam(
        pi(nat(), family(0)),
        lam(pi(nat(), nat()), Term::Succ(at_zero).arc()),
    );
    let fold = data(
        DataOp::Eliminate(0, 0),
        vec![lam(family(0), nat()), zero(), step, node],
    );
    assert_eq!(k.normalize(&fold).unwrap(), Term::Succ(zero()).arc());
}

#[test]
fn neutral_general_elimination_composes_with_existing_eliminators() {
    let mut k = Kernel::default();
    k.declare_data(0, naturals()).unwrap();
    let count = data(
        DataOp::Eliminate(0, 0),
        vec![
            lam(family(0), nat()),
            zero(),
            lam(family(0), lam(nat(), Term::Succ(v(0)).arc())),
            v(0),
        ],
    );
    let body = Term::NatElim(
        0,
        lam(nat(), nat()),
        zero(),
        lam(nat(), lam(nat(), v(0))),
        count,
    )
    .arc();
    let function = lam(family(0), body);
    assert_eq!(k.infer(&function).unwrap(), pi(family(0), nat()));
    k.normalize(&function).unwrap();
    k.check(&k.normalize(&function).unwrap(), &pi(family(0), nat()))
        .unwrap();
}

#[test]
fn malformed_declarations_and_eliminators_never_enter_environment() {
    let mut k = Kernel::default();
    let mut bad = naturals();
    bad.constructors[1].fields = vec![v(0)];
    assert!(k.declare_data(0, bad).is_err());
    assert!(k.data_declaration(0).is_err());
    k.declare_data(0, naturals()).unwrap();
    assert_eq!(
        k.declare_data(0, naturals()),
        Err(Error::DuplicateInductive(0))
    );
    let z = data(DataOp::Constructor(0, 0), vec![]);
    assert!(k
        .infer(&data(
            DataOp::Eliminate(0, 0),
            vec![lam(family(0), nat()), zero(), zero(), z.clone()]
        ))
        .is_err());
    assert!(k
        .infer(&data(
            DataOp::Eliminate(0, 0),
            vec![lam(family(0), nat()), zero(), z]
        ))
        .is_err());
    assert!(k.infer(&data(DataOp::Constructor(0, 9), vec![])).is_err());
    assert!(Kernel::new(0).declare_data(0, naturals()).is_err());
}

#[test]
fn family_dependency_tracking_includes_constructor_field_types() {
    let mut k = Kernel::default();
    k.declare_axiom(4, Term::Universe(0).arc()).unwrap();
    k.declare_data(
        0,
        DataDecl {
            parameters: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![ConstructorDecl {
                fields: vec![Term::Global(4).arc()],
                indices: vec![],
            }],
        },
    )
    .unwrap();
    assert_eq!(
        k.axiom_dependencies(&family(0))
            .unwrap()
            .into_iter()
            .collect::<Vec<_>>(),
        vec![4]
    );
}

#[test]
fn rejects_self_elimination_in_a_constructor_signature() {
    let mut k = Kernel::default();
    let mut bad = naturals();
    bad.constructors[1].fields = vec![
        family(0),
        data(DataOp::Absurd(0), vec![Term::Universe(0).arc(), v(0)]),
    ];
    assert_eq!(k.declare_data(0, bad), Err(Error::InvalidPositivity));
    assert!(k.data_declaration(0).is_err());
}

#[test]
fn recursive_occurrences_in_result_indices_are_rejected() {
    let mut k = Kernel::default();
    let declaration = DataDecl {
        parameters: vec![],
        indices: vec![Term::Universe(0).arc()],
        level: 0,
        constructors: vec![ConstructorDecl {
            fields: vec![],
            indices: vec![data(DataOp::Type(0), vec![nat()])],
        }],
    };
    assert_eq!(
        k.declare_data(0, declaration),
        Err(Error::InvalidPositivity)
    );
}

#[test]
fn runtime_projection_preserves_general_constructor_identity() {
    let mut k = Kernel::default();
    k.declare_data(0, naturals()).unwrap();
    let zero = data(DataOp::Constructor(0, 0), vec![]);
    assert_eq!(
        k.erase(&zero).unwrap(),
        deppy_core::RuntimeTerm::Data(0, 0, vec![])
    );
    assert!(matches!(
        k.runtime_signature(&zero).unwrap().result,
        deppy_core::RuntimeType::Data(0, _, _)
    ));
}
