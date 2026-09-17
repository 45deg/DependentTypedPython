use deppy_core::{Definition, Error, Kernel, Relevance, Term as T};
fn nat() -> deppy_core::Tm {
    T::Nat.arc()
}
#[test]
fn globals_unfold_in_terms_types_and_closures() {
    let mut k = Kernel::default();
    k.define(
        0,
        Definition {
            ty: T::Universe(0).arc(),
            body: nat(),
        },
    )
    .unwrap();
    k.define(
        1,
        Definition {
            ty: T::Global(0).arc(),
            body: T::Zero.arc(),
        },
    )
    .unwrap();
    let f = T::Lam {
        relevance: Relevance::Runtime,
        domain: T::Global(0).arc(),
        body: T::Succ(T::Global(1).arc()).arc(),
    }
    .arc();
    let ty = k.infer(&f).unwrap();
    k.define(2, Definition { ty, body: f }).unwrap();
    let call = T::App {
        function: T::Global(2).arc(),
        argument: T::Zero.arc(),
    }
    .arc();
    assert_eq!(k.normalize(&call).unwrap(), T::Succ(T::Zero.arc()).arc());
    assert!(k
        .equivalent(&T::Global(1).arc(), &T::Zero.arc(), &nat())
        .unwrap());
}
#[test]
fn rejects_self_forward_and_open_definitions_atomically() {
    let mut k = Kernel::default();
    for body in [
        T::Global(0).arc(),
        T::Global(1).arc(),
        T::Var(0).arc(),
        T::Universe(0).arc(),
    ] {
        assert!(k.define(0, Definition { ty: nat(), body }).is_err());
        assert!(matches!(k.definition(0), Err(Error::UnknownDefinition(0))));
    }
    k.define(
        0,
        Definition {
            ty: nat(),
            body: T::Zero.arc(),
        },
    )
    .unwrap();
    assert!(matches!(
        k.define(
            0,
            Definition {
                ty: nat(),
                body: T::Zero.arc()
            }
        ),
        Err(Error::DuplicateDefinition(0))
    ));
    assert!(k
        .define(
            1,
            Definition {
                ty: T::Zero.arc(),
                body: T::Zero.arc()
            }
        )
        .is_err());
}
#[test]
fn discarded_invalid_global_references_are_checked() {
    let mut k = Kernel::default();
    let bad = T::Let {
        ty: nat(),
        value: T::Global(99).arc(),
        body: T::Zero.arc(),
    }
    .arc();
    assert_eq!(k.normalize(&bad), Err(Error::UnknownDefinition(99)));
    assert_eq!(
        k.define(
            0,
            Definition {
                ty: nat(),
                body: bad
            }
        ),
        Err(Error::UnknownDefinition(99))
    );
}
#[test]
fn snapshots_do_not_gain_later_definitions() {
    let mut k = Kernel::default();
    let snapshot = k.clone();
    k.define(
        0,
        Definition {
            ty: nat(),
            body: T::Zero.arc(),
        },
    )
    .unwrap();
    assert_eq!(
        snapshot.infer(&T::Global(0).arc()),
        Err(Error::UnknownDefinition(0))
    );
    assert!(k.infer(&T::Global(0).arc()).is_ok());
}
#[test]
fn global_evaluation_consumes_the_operation_budget() {
    let mut k = Kernel::new(30);
    k.define(
        0,
        Definition {
            ty: nat(),
            body: T::Zero.arc(),
        },
    )
    .unwrap();
    for id in 1..40 {
        k.define(
            id,
            Definition {
                ty: nat(),
                body: T::Global(id - 1).arc(),
            },
        )
        .unwrap();
    }
    assert_eq!(
        k.normalize(&T::Global(39).arc()),
        Err(Error::BudgetExceeded)
    );
}
