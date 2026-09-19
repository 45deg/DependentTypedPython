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
        body: Term::Fin {
            bound: Term::Var(0).arc(),
        }
        .arc(),
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
            Box::new(RuntimeTerm::Prim("zero", vec![]))
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
