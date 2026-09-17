use deppy_core::{Error, Kernel, Relevance, Term, Tm};
use Relevance::{Erased, Runtime};
fn u(n: u32) -> Tm {
    Term::Universe(n).arc()
}
fn v(n: usize) -> Tm {
    Term::Var(n).arc()
}
fn pi(r: Relevance, a: Tm, b: Tm) -> Tm {
    Term::Pi {
        relevance: r,
        domain: a,
        codomain: b,
    }
    .arc()
}
fn lam(r: Relevance, a: Tm, b: Tm) -> Tm {
    Term::Lam {
        relevance: r,
        domain: a,
        body: b,
    }
    .arc()
}
fn app(f: Tm, a: Tm) -> Tm {
    Term::App {
        function: f,
        argument: a,
    }
    .arc()
}
fn let_(ty: Tm, value: Tm, body: Tm) -> Tm {
    Term::Let { ty, value, body }.arc()
}
fn identity() -> Tm {
    lam(Erased, u(0), lam(Runtime, v(0), v(0)))
}
fn identity_type() -> Tm {
    pi(Erased, u(0), pi(Runtime, v(0), v(1)))
}

#[test]
fn universe_hierarchy() {
    for n in 0..16 {
        assert_eq!(Kernel::default().infer(&u(n)), Ok(u(n + 1)));
    }
}
#[test]
fn rejects_type_in_type_and_cumulativity() {
    let k = Kernel::default();
    assert!(matches!(
        k.check(&u(0), &u(0)),
        Err(Error::TypeMismatch { .. })
    ));
    assert!(matches!(
        k.check(&u(0), &u(2)),
        Err(Error::TypeMismatch { .. })
    ));
}
#[test]
fn rejects_level_overflow() {
    assert_eq!(
        Kernel::default().infer(&u(u32::MAX)),
        Err(Error::UniverseOverflow)
    );
}
#[test]
fn dependent_identity() {
    let k = Kernel::default();
    assert_eq!(k.infer(&identity()), Ok(identity_type()));
    assert_eq!(k.check(&identity(), &identity_type()), Ok(()));
    assert_eq!(k.infer(&identity_type()), Ok(u(1)));
}
#[test]
fn pi_uses_maximum_level() {
    let k = Kernel::default();
    assert_eq!(k.infer(&pi(Runtime, u(2), u(0))), Ok(u(3)));
    assert_eq!(k.infer(&pi(Runtime, u(0), u(2))), Ok(u(3)));
}
#[test]
fn beta_reduction() {
    let term = app(lam(Runtime, u(1), v(0)), u(0));
    assert_eq!(Kernel::default().normalize(&term), Ok(u(0)));
}
#[test]
fn closure_keeps_outer_binding_under_shadowing() {
    let term = app(
        app(lam(Runtime, u(2), lam(Runtime, u(1), v(1))), u(1)),
        u(0),
    );
    assert_eq!(Kernel::default().normalize(&term), Ok(u(1)));
}
#[test]
fn zeta_substitutes_in_result_type() {
    let term = let_(u(1), u(0), lam(Runtime, v(0), v(0)));
    let k = Kernel::default();
    assert_eq!(k.infer(&term), Ok(pi(Runtime, u(0), u(0))));
    assert_eq!(k.normalize(&term), Ok(lam(Runtime, u(0), v(0))));
}
#[test]
fn dependent_application_substitutes_argument() {
    // Type-level identity at Type1, instantiated with Type0 and a small type A.
    let id = lam(Erased, u(1), lam(Runtime, v(0), v(0)));
    let term = lam(Erased, u(0), app(app(id, u(0)), v(0)));
    assert_eq!(
        Kernel::default().normalize(&term),
        Ok(lam(Erased, u(0), v(0)))
    );
}
#[test]
fn function_eta() {
    // lambda A. lambda f: A -> A. f  ==  lambda A. lambda f. lambda x. f x
    let fty = pi(Runtime, v(0), v(1));
    let left = lam(Erased, u(0), lam(Runtime, fty.clone(), v(0)));
    let right = lam(
        Erased,
        u(0),
        lam(Runtime, fty.clone(), lam(Runtime, v(1), app(v(1), v(0)))),
    );
    let ty = pi(Erased, u(0), pi(Runtime, fty, pi(Runtime, v(1), v(2))));
    assert_eq!(Kernel::default().equivalent(&left, &right, &ty), Ok(true));
}
#[test]
fn distinct_neutrals_are_not_equal() {
    let left = lam(Erased, u(0), lam(Runtime, v(0), lam(Runtime, v(1), v(1))));
    let right = lam(Erased, u(0), lam(Runtime, v(0), lam(Runtime, v(1), v(0))));
    let ty = pi(Erased, u(0), pi(Runtime, v(0), pi(Runtime, v(1), v(2))));
    assert_eq!(Kernel::default().equivalent(&left, &right, &ty), Ok(false));
}
#[test]
fn rejects_unbound_and_extreme_indices() {
    for i in [0, 1, usize::MAX] {
        assert_eq!(
            Kernel::default().infer(&v(i)),
            Err(Error::UnboundVariable(i))
        );
    }
    assert_eq!(
        Kernel::default().infer(&lam(Runtime, u(0), v(1))),
        Err(Error::UnboundVariable(1))
    );
}
#[test]
fn rejects_non_type_domain_and_codomain() {
    let k = Kernel::default();
    // A: Type, x: A; x is not a type.
    let wrap = |t| lam(Erased, u(0), lam(Runtime, v(0), t));
    assert_eq!(
        k.infer(&wrap(pi(Runtime, v(0), u(0)))),
        Err(Error::ExpectedUniverse)
    );
    assert_eq!(
        k.infer(&wrap(pi(Runtime, u(0), v(1)))),
        Err(Error::ExpectedUniverse)
    );
    assert_eq!(
        k.infer(&wrap(lam(Runtime, v(0), v(0)))),
        Err(Error::ExpectedUniverse)
    );
}
#[test]
fn rejects_bad_application_before_evaluation() {
    let k = Kernel::default();
    assert_eq!(k.normalize(&app(u(0), u(0))), Err(Error::ExpectedFunction));
    assert!(matches!(
        k.infer(&app(identity(), u(0))),
        Err(Error::TypeMismatch { .. })
    ));
}
#[test]
fn rejects_bad_let_annotation_and_value() {
    let k = Kernel::default();
    assert!(matches!(
        k.infer(&let_(u(0), u(0), v(0))),
        Err(Error::TypeMismatch { .. })
    ));
    assert_eq!(
        k.infer(&let_(identity(), identity(), v(0))),
        Err(Error::ExpectedUniverse)
    );
}
#[test]
fn relevance_is_part_of_function_type() {
    let wrong = pi(Runtime, u(0), pi(Runtime, v(0), v(1)));
    assert!(matches!(
        Kernel::default().check(&identity(), &wrong),
        Err(Error::TypeMismatch { .. })
    ));
}
#[test]
fn conversion_does_not_accept_ill_typed_inputs() {
    let k = Kernel::default();
    assert!(k.equivalent(&u(0), &u(0), &u(0)).is_err());
    assert_eq!(
        k.check(&identity(), &identity()),
        Err(Error::ExpectedUniverse)
    );
}
#[test]
fn rejects_self_application_before_normalization() {
    let omega = lam(Runtime, u(0), app(v(0), v(0)));
    assert_eq!(
        Kernel::default().normalize(&app(omega.clone(), omega)),
        Err(Error::ExpectedFunction)
    );
}
#[test]
fn exhausted_budget_is_never_success() {
    assert_eq!(Kernel::new(0).infer(&u(0)), Err(Error::BudgetExceeded));
    assert_eq!(Kernel::new(1).normalize(&u(0)), Err(Error::BudgetExceeded));
    assert_eq!(
        Kernel::new(1).equivalent(&u(0), &u(0), &u(1)),
        Err(Error::BudgetExceeded)
    );
}
