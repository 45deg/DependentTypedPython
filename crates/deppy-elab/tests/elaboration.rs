use deppy_core::{Kernel, Relevance, Term};
use deppy_elab::{
    Elaborator, Error, Expr as E,
    Plicity::{Explicit as X, Implicit as I},
};
fn n(name: &str) -> E {
    E::name(name)
}
fn u(level: u32) -> E {
    E::Universe(level)
}
fn identity() -> E {
    E::lam("A", I, Some(u(0)), E::lam("x", X, Some(n("A")), n("x")))
}
fn identity_type() -> E {
    E::pi("A", I, u(0), E::pi("x", X, n("A"), n("A")))
}
fn in_scope(body: E) -> E {
    E::lam("A", I, Some(u(0)), E::lam("x", X, Some(n("A")), body))
}

#[test]
fn synthesizes_dependent_identity() {
    let result = Elaborator::default().infer(&identity()).unwrap();
    let expected = Elaborator::default().infer(&identity_type()).unwrap();
    assert_eq!(result.ty, expected.term);
    Kernel::default().check(&result.term, &result.ty).unwrap();
}
#[test]
fn checks_unannotated_lambdas_from_expected_pi() {
    let expr = E::lam("B", I, None, E::lam("value", X, None, n("value")));
    let result = Elaborator::default()
        .check(&expr, &identity_type())
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        Elaborator::default().infer(&identity()).unwrap().term
    );
}
#[test]
fn inserts_and_solves_implicit_type_from_argument() {
    let expr = in_scope(identity().app(n("x")));
    let result = Elaborator::default().infer(&expr).unwrap();
    let expected = Elaborator::default().infer(&identity()).unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        expected.term
    );
    assert_eq!(result.ty, expected.ty);
}
#[test]
fn explicit_implicit_argument() {
    let expr = in_scope(identity().implicit(n("A")).app(n("x")));
    let result = Elaborator::default().infer(&expr).unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        Elaborator::default().infer(&identity()).unwrap().term
    );
}
#[test]
fn hole_in_explicit_specialization_is_constrained_by_later_argument() {
    let result = Elaborator::default()
        .infer(&in_scope(identity().implicit(E::Hole).app(n("x"))))
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        Elaborator::default().infer(&identity()).unwrap().term
    );
}
#[test]
fn expected_return_type_solves_an_implicit_argument() {
    // Given f: {A: Type0} -> Type0 -> A, checking f(Type0) would be
    // ill-typed; use Type1 as its explicit domain instead.
    let fty = E::pi("B", I, u(0), E::pi("tag", X, u(1), n("B")));
    let body = n("f").app(u(0)).ann(n("A"));
    let expr = E::lam("A", I, Some(u(0)), E::lam("f", X, Some(fty), body));
    let result = Elaborator::default().infer(&expr).unwrap();
    Kernel::default().check(&result.term, &result.ty).unwrap();
    // The neutral call survives normalization, with an explicit core type argument.
    let Term::Lam { body, .. } = result.term.as_ref() else {
        panic!()
    };
    let Term::Lam { body, .. } = body.as_ref() else {
        panic!()
    };
    let Term::App { function, .. } = body.as_ref() else {
        panic!()
    };
    let Term::App { argument, .. } = function.as_ref() else {
        panic!()
    };
    assert_eq!(argument.as_ref(), &Term::Var(1));
}
#[test]
fn multiple_implicit_arguments() {
    let first = E::lam(
        "A",
        I,
        Some(u(0)),
        E::lam(
            "B",
            I,
            Some(u(0)),
            E::lam("x", X, Some(n("A")), E::lam("y", X, Some(n("B")), n("x"))),
        ),
    );
    let expr = in_scope(first.app(n("x")).app(n("x")));
    assert_eq!(
        Kernel::default()
            .normalize(&Elaborator::default().infer(&expr).unwrap().term)
            .unwrap(),
        Elaborator::default().infer(&identity()).unwrap().term
    );
}
#[test]
fn concrete_universe_identity() {
    let id = E::lam("A", I, Some(u(2)), E::lam("x", X, Some(n("A")), n("x")));
    let result = Elaborator::default().infer(&id.app(u(0))).unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        Term::Universe(0).arc()
    );
    assert_eq!(result.ty, Term::Universe(1).arc());
}
#[test]
fn beta_conversion_in_annotation() {
    let ty = E::lam("T", X, Some(u(1)), n("T")).app(u(0));
    let result = Elaborator::default()
        .infer(&E::lam("A", X, Some(ty), n("A")))
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.ty).unwrap(),
        Term::Pi {
            relevance: Relevance::Runtime,
            domain: Term::Universe(0).arc(),
            codomain: Term::Universe(0).arc()
        }
        .arc()
    );
}
#[test]
fn resolves_shadowing_to_nearest_binder() {
    let expr = E::lam(
        "A",
        I,
        Some(u(0)),
        E::lam("x", X, Some(n("A")), E::lam("x", X, Some(n("A")), n("x"))),
    );
    let result = Elaborator::default().infer(&expr).unwrap();
    let Term::Lam { body, .. } = result.term.as_ref() else {
        panic!()
    };
    let Term::Lam { body, .. } = body.as_ref() else {
        panic!()
    };
    let Term::Lam { body, .. } = body.as_ref() else {
        panic!()
    };
    assert_eq!(body.as_ref(), &Term::Var(0));
}
#[test]
fn rejects_unknown_names_and_forward_references() {
    assert!(matches!(
        Elaborator::default().infer(&n("missing")),
        Err(Error::UnknownName(_))
    ));
    let expr = E::pi("x", X, n("A"), E::pi("A", I, u(0), n("A")));
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::UnknownName(_))
    ));
}
#[test]
fn rejects_unannotated_synthesis() {
    assert!(matches!(
        Elaborator::default().infer(&E::lam("x", X, None, n("x"))),
        Err(Error::AnnotationRequired)
    ));
    assert!(matches!(
        Elaborator::default().infer(&E::Hole),
        Err(Error::AnnotationRequired)
    ));
}
#[test]
fn rejects_unresolved_holes_even_when_beta_erased() {
    assert!(matches!(
        Elaborator::default().check(&E::Hole, &u(0)),
        Err(Error::UnsolvedMeta { .. })
    ));
    let expr = E::lam("ignored", X, Some(u(1)), u(0)).app(E::Hole);
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn rejects_underconstrained_implicit_argument() {
    let f = E::lam("A", I, Some(u(0)), E::lam("tag", X, Some(u(1)), u(0)));
    assert!(matches!(
        Elaborator::default().infer(&f.app(u(0))),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn rejects_non_cumulative_universes() {
    let elab = Elaborator::default();
    assert!(matches!(elab.check(&u(0), &u(0)), Err(Error::CannotUnify)));
    assert!(matches!(elab.check(&u(0), &u(2)), Err(Error::CannotUnify)));
    assert!(matches!(
        elab.infer(&u(u32::MAX)),
        Err(Error::UniverseOverflow)
    ));
}
#[test]
fn rejects_wrong_argument_type_and_non_function() {
    let elab = Elaborator::default();
    assert!(matches!(
        elab.infer(&identity().app(u(0))),
        Err(Error::Kernel(_))
    ));
    assert!(matches!(
        elab.infer(&u(0).app(u(0))),
        Err(Error::ExpectedFunction)
    ));
}
#[test]
fn rejects_plicity_and_lambda_annotation_mismatches() {
    let elab = Elaborator::default();
    let wrong = E::lam("A", X, None, E::lam("x", X, None, n("x")));
    assert!(matches!(
        elab.check(&wrong, &identity_type()),
        Err(Error::PlicityMismatch)
    ));
    let wrong = E::lam("A", I, Some(u(1)), E::lam("x", X, None, n("x")));
    assert!(matches!(
        elab.check(&wrong, &identity_type()),
        Err(Error::CannotUnify)
    ));
    let wrong = E::lam("A", X, Some(u(1)), n("A")).implicit(u(0));
    assert!(matches!(elab.infer(&wrong), Err(Error::PlicityMismatch)));
}
#[test]
fn rejects_non_type_annotation() {
    let expr = in_scope(E::lam("bad", X, Some(n("x")), n("bad")));
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::ExpectedUniverse)
    ));
}
#[test]
fn state_does_not_leak_between_calls() {
    let elab = Elaborator::default();
    assert!(elab.check(&E::Hole, &u(0)).is_err());
    assert!(elab.infer(&in_scope(identity().app(n("x")))).is_ok());
}
#[test]
fn budget_exhaustion_fails_closed() {
    assert!(matches!(
        Elaborator::new(0).infer(&u(0)),
        Err(Error::BudgetExceeded)
    ));
    assert!(Elaborator::new(8)
        .infer(&in_scope(identity().app(n("x"))))
        .is_err());
}

#[test]
fn rejects_scope_escape_from_a_later_lambda_binder() {
    // f : {A : Type0} -> (B : Type0 -> A) -> Type0.
    // Choosing A = (B -> B) would leak the callback's bound variable B.
    let callback_ty = E::pi("B", X, u(0), n("A"));
    let fty = E::pi("A", I, u(0), E::pi("callback", X, callback_ty, u(0)));
    let callback = E::lam(
        "B",
        X,
        Some(u(0)),
        E::lam("x", X, Some(n("B")), n("x")).ann(E::pi("x", X, n("B"), n("B"))),
    );
    let expr = E::lam("f", X, Some(fty), n("f").app(callback));
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::ScopeEscape)
    ));
}

#[test]
fn unknown_function_type_is_not_guessed() {
    // A hole alone does not justify treating its type as a function.
    let expr = E::Hole.ann(u(0)).app(u(0));
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::ExpectedFunction)
    ));
}
