use deppy_core::{Definition, Error, Kernel, Term};
fn nat() -> deppy_core::Tm {
    Term::Nat.arc()
}
fn zero() -> deppy_core::Tm {
    Term::Zero.arc()
}
fn one() -> deppy_core::Tm {
    Term::Succ(zero()).arc()
}

#[test]
fn axioms_are_explicit_atomic_opaque_and_do_not_reflect_equality() {
    let mut k = Kernel::default();
    assert!(k.declare_axiom(0, zero()).is_err());
    assert!(matches!(k.definition(0), Err(Error::UnknownDefinition(0))));
    let snapshot = k.clone();
    let proposition = Term::Eq {
        ty: nat(),
        left: zero(),
        right: one(),
    }
    .arc();
    k.declare_axiom(0, proposition.clone()).unwrap();
    let proof = Term::Global(0).arc();
    assert_eq!(k.infer(&proof).unwrap(), proposition);
    assert_eq!(k.normalize(&proof).unwrap(), proof);
    assert!(!k.equivalent(&zero(), &one(), &nat()).unwrap());
    assert!(k
        .check(
            &Term::Refl {
                ty: nat(),
                value: zero()
            }
            .arc(),
            &proposition
        )
        .is_err());
    let motive = Term::Lam {
        relevance: deppy_core::Relevance::Runtime,
        domain: nat(),
        body: Term::Lam {
            relevance: deppy_core::Relevance::Runtime,
            domain: Term::Eq {
                ty: nat(),
                left: zero(),
                right: Term::Var(0).arc(),
            }
            .arc(),
            body: nat(),
        }
        .arc(),
    }
    .arc();
    let transport = Term::J {
        level: 0,
        ty: nat(),
        left: zero(),
        motive,
        base: zero(),
        right: one(),
        proof: proof.clone(),
    }
    .arc();
    assert!(matches!(
        k.normalize(&transport).unwrap().as_ref(),
        Term::J { .. }
    ));
    assert!(snapshot.infer(&proof).is_err());
    assert!(matches!(
        k.declare_axiom(0, nat()),
        Err(Error::DuplicateDefinition(0))
    ));
    assert!(matches!(
        k.define(
            0,
            Definition {
                ty: nat(),
                body: zero()
            }
        ),
        Err(Error::DuplicateDefinition(0))
    ));
    assert_eq!(
        k.erase(&proof).unwrap(),
        deppy_core::RuntimeTerm::Prim("erased_proof", vec![])
    );
    assert!(matches!(
        k.erase(&transport),
        Err(Error::AxiomHasNoRuntimeValue(0))
    ));
    k.define(
        1,
        Definition {
            ty: proposition,
            body: proof,
        },
    )
    .unwrap();
    assert_eq!(
        k.axiom_dependencies(&Term::Global(1).arc())
            .unwrap()
            .into_iter()
            .collect::<Vec<_>>(),
        vec![0]
    );
}

#[test]
fn opaque_types_are_distinct_and_dependencies_include_types() {
    let mut k = Kernel::default();
    k.declare_axiom(0, Term::Universe(0).arc()).unwrap();
    k.declare_axiom(1, Term::Universe(0).arc()).unwrap();
    k.declare_axiom(2, Term::Global(0).arc()).unwrap();
    assert!(k
        .check(&Term::Global(2).arc(), &Term::Global(1).arc())
        .is_err());
    assert_eq!(
        k.axiom_dependencies(&Term::Global(2).arc())
            .unwrap()
            .into_iter()
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    assert!(k.declare_axiom(3, Term::Global(3).arc()).is_err());
    assert!(k.declare_axiom(3, Term::Universe(u32::MAX).arc()).is_err());
}
