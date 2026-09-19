use deppy_core::{Error, Kernel, Relevance, RuntimeTerm, Term};

#[test]
fn runtime_use_of_erased_index_is_rejected_but_type_use_is_allowed() {
    let kernel = Kernel::default();
    let bad = Term::Lam {
        relevance: Relevance::Erased,
        domain: Term::Nat.arc(),
        body: Term::Var(0).arc(),
    }
    .arc();
    kernel.infer(&bad).unwrap();
    assert_eq!(kernel.erase(&bad), Err(Error::ErasedVariableUsed(0)));
    let good = Term::Lam {
        relevance: Relevance::Erased,
        domain: Term::Nat.arc(),
        body: Term::Fin(Term::Var(0).arc()).arc(),
    }
    .arc();
    assert_eq!(kernel.erase(&good).unwrap(), RuntimeTerm::Unit);
}

#[test]
fn retained_indices_are_renumbered_and_erased_arguments_disappear() {
    let kernel = Kernel::default();
    let term = Term::Lam {
        relevance: Relevance::Runtime,
        domain: Term::Nat.arc(),
        body: Term::Lam {
            relevance: Relevance::Erased,
            domain: Term::Nat.arc(),
            body: Term::Var(1).arc(),
        }
        .arc(),
    }
    .arc();
    assert_eq!(
        kernel.erase(&term).unwrap(),
        RuntimeTerm::Lam(Box::new(RuntimeTerm::Var(0)))
    );
    let applied = Term::App {
        function: Term::App {
            function: term,
            argument: Term::Zero.arc(),
        }
        .arc(),
        argument: Term::Succ(Term::Zero.arc()).arc(),
    }
    .arc();
    assert_eq!(
        kernel.erase(&applied).unwrap(),
        RuntimeTerm::App(
            Box::new(RuntimeTerm::Lam(Box::new(RuntimeTerm::Var(0)))),
            Box::new(RuntimeTerm::Data(deppy_core::standard::NAT, 0, vec![]))
        )
    );
}

#[test]
fn unused_invalid_terms_are_still_kernel_checked() {
    let bad = Term::App {
        function: Term::Lam {
            relevance: Relevance::Erased,
            domain: Term::Nat.arc(),
            body: Term::Zero.arc(),
        }
        .arc(),
        argument: Term::Universe(0).arc(),
    }
    .arc();
    assert!(matches!(
        Kernel::default().erase(&bad),
        Err(Error::TypeMismatch { .. })
    ));
}

#[test]
fn referenced_definitions_cannot_hide_erased_runtime_usage() {
    let mut kernel = Kernel::default();
    let body = Term::Lam {
        relevance: Relevance::Erased,
        domain: Term::Nat.arc(),
        body: Term::Var(0).arc(),
    }
    .arc();
    let ty = kernel.infer(&body).unwrap();
    kernel
        .define(0, deppy_core::Definition { ty, body })
        .unwrap();
    assert_eq!(
        kernel.erase(&Term::Global(0).arc()),
        Err(Error::ErasedVariableUsed(0))
    );
}

fn proposition() -> deppy_core::Tm {
    Term::Eq {
        ty: Term::Nat.arc(),
        left: Term::Zero.arc(),
        right: Term::Zero.arc(),
    }
    .arc()
}
fn lam(relevance: Relevance, domain: deppy_core::Tm, body: deppy_core::Tm) -> deppy_core::Tm {
    Term::Lam {
        relevance,
        domain,
        body,
    }
    .arc()
}
fn observe(proof: deppy_core::Tm) -> deppy_core::Tm {
    Term::J {
        level: 0,
        ty: Term::Nat.arc(),
        left: Term::Zero.arc(),
        motive: lam(
            Relevance::Runtime,
            Term::Nat.arc(),
            lam(
                Relevance::Runtime,
                Term::Eq {
                    ty: Term::Nat.arc(),
                    left: Term::Zero.arc(),
                    right: Term::Var(0).arc(),
                }
                .arc(),
                Term::Nat.arc(),
            ),
        ),
        base: Term::Zero.arc(),
        right: Term::Zero.arc(),
        proof,
    }
    .arc()
}

#[test]
fn erased_proofs_may_flow_to_proof_results_but_not_computational_j() {
    let k = Kernel::default();
    let erased = lam(Relevance::Erased, proposition(), Term::Var(0).arc());
    assert_eq!(
        k.erase(&erased).unwrap(),
        RuntimeTerm::Prim("erased_proof", vec![])
    );
    let computational = lam(
        Relevance::Erased,
        proposition(),
        observe(Term::Var(0).arc()),
    );
    k.infer(&computational).unwrap();
    assert_eq!(k.erase(&computational), Err(Error::ErasedVariableUsed(0)));
    // Checking still precedes discarding the proof body.
    let invalid = lam(
        Relevance::Erased,
        proposition(),
        Term::App {
            function: Term::Var(0).arc(),
            argument: Term::Zero.arc(),
        }
        .arc(),
    );
    assert!(k.erase(&invalid).is_err());
}

#[test]
fn computational_uses_do_not_reuse_discarded_global_proofs() {
    let mut k = Kernel::default();
    k.declare_axiom(0, proposition()).unwrap();
    k.define(
        1,
        deppy_core::Definition {
            ty: proposition(),
            body: Term::Global(0).arc(),
        },
    )
    .unwrap();
    assert_eq!(
        k.erase(&Term::Global(1).arc()).unwrap(),
        RuntimeTerm::Prim("erased_proof", vec![])
    );
    assert_eq!(
        k.erase(&observe(Term::Global(1).arc())),
        Err(Error::AxiomHasNoRuntimeValue(0))
    );

    // A transparent, computational proof remains usable, even though its
    // separately emitted declaration has an erased result.
    k.define(
        2,
        deppy_core::Definition {
            ty: proposition(),
            body: Term::Refl {
                ty: Term::Nat.arc(),
                value: Term::Zero.arc(),
            }
            .arc(),
        },
    )
    .unwrap();
    assert_eq!(
        k.erase(&observe(Term::Global(2).arc())).unwrap(),
        RuntimeTerm::Prim(
            "j",
            vec![
                RuntimeTerm::Data(deppy_core::standard::NAT, 0, vec![]),
                RuntimeTerm::Prim("refl", vec![]),
            ]
        )
    );
}

#[test]
fn proof_lets_are_removed_only_when_their_runtime_uses_disappear() {
    let mut k = Kernel::default();
    k.declare_axiom(0, proposition()).unwrap();
    let binding = |body| {
        Term::Let {
            ty: proposition(),
            value: Term::Global(0).arc(),
            body,
        }
        .arc()
    };
    assert_eq!(
        k.erase(&binding(Term::Zero.arc())).unwrap(),
        RuntimeTerm::Data(deppy_core::standard::NAT, 0, vec![])
    );
    assert_eq!(
        k.erase(&binding(observe(Term::Var(0).arc()))),
        Err(Error::AxiomHasNoRuntimeValue(0))
    );
    let renumbered = lam(
        Relevance::Runtime,
        Term::Nat.arc(),
        binding(Term::Var(1).arc()),
    );
    assert_eq!(
        k.erase(&renumbered).unwrap(),
        RuntimeTerm::Lam(Box::new(RuntimeTerm::Var(0)))
    );
}
