use deppy_core::{Error, Kernel, Relevance::Runtime, Term as T, Tm};
fn n() -> Tm {
    T::Nat.arc()
}
fn z() -> Tm {
    T::Zero.arc()
}
fn v(i: usize) -> Tm {
    T::Var(i).arc()
}
fn u(i: u32) -> Tm {
    T::Universe(i).arc()
}
fn s(t: Tm) -> Tm {
    T::Succ(t).arc()
}
fn lam(a: Tm, b: Tm) -> Tm {
    T::Lam {
        relevance: Runtime,
        domain: a,
        body: b,
    }
    .arc()
}
fn pi(a: Tm, b: Tm) -> Tm {
    T::Pi {
        relevance: Runtime,
        domain: a,
        codomain: b,
    }
    .arc()
}
fn app(f: Tm, x: Tm) -> Tm {
    T::App {
        function: f,
        argument: x,
    }
    .arc()
}
fn elim(level: u32, motive: Tm, zero: Tm, step: Tm, scrutinee: Tm) -> Tm {
    T::NatElim {
        level,
        motive,
        zero,
        step,
        scrutinee,
    }
    .arc()
}
fn copy(t: Tm) -> Tm {
    elim(0, lam(n(), n()), z(), lam(n(), lam(n(), s(v(0)))), t)
}

#[test]
fn iota_zero_and_successor() {
    for t in [z(), s(z()), s(s(z()))] {
        assert_eq!(Kernel::default().normalize(&copy(t.clone())).unwrap(), t);
    }
}
#[test]
fn step_receives_predecessor_not_current_number() {
    let pred = elim(0, lam(n(), n()), z(), lam(n(), lam(n(), v(1))), s(s(z())));
    assert_eq!(Kernel::default().normalize(&pred).unwrap(), s(z()));
}
#[test]
fn neutral_eliminator_roundtrips_without_nat_eta() {
    let k = Kernel::default();
    let term = lam(n(), copy(v(0)));
    assert_eq!(k.normalize(&term).unwrap(), term);
    assert!(k.equivalent(&term, &term, &pi(n(), n())).unwrap());
    assert!(!k.equivalent(&term, &lam(n(), v(0)), &pi(n(), n())).unwrap());
    let next = lam(n(), copy(s(v(0))));
    assert_eq!(k.normalize(&next).unwrap(), lam(n(), s(copy(v(0)))));
}
#[test]
fn elimination_into_a_higher_universe() {
    let term = elim(
        1,
        lam(n(), u(0)),
        n(),
        lam(n(), lam(u(0), pi(n(), n()))),
        s(z()),
    );
    assert_eq!(Kernel::default().infer(&term).unwrap(), u(0));
    assert_eq!(Kernel::default().normalize(&term).unwrap(), pi(n(), n()));
}
// A family with P Z = Nat and P (S n) = Nat -> Nat.
fn family() -> Tm {
    lam(
        n(),
        elim(
            1,
            lam(n(), u(0)),
            n(),
            lam(n(), lam(u(0), pi(n(), n()))),
            v(0),
        ),
    )
}
#[test]
fn dependent_branch_type_and_induction_hypothesis() {
    let step = lam(n(), lam(app(family(), v(0)), lam(n(), v(0))));
    let k = Kernel::default();
    let term = elim(0, family(), z(), step.clone(), s(z()));
    assert_eq!(k.infer(&term).unwrap(), pi(n(), n()));
    assert_eq!(k.normalize(&term).unwrap(), lam(n(), v(0)));
    let term = elim(0, family(), z(), step, z());
    assert_eq!(k.infer(&term).unwrap(), n());
    assert_eq!(k.normalize(&term).unwrap(), z());
}
#[test]
fn symbolic_motive_survives_nested_binders() {
    // lambda P. lambda z. lambda step. lambda n. elim P z step n
    let step_ty = pi(n(), pi(app(v(2), v(0)), app(v(3), s(v(1)))));
    let term = lam(
        pi(n(), u(0)),
        lam(
            app(v(0), z()),
            lam(step_ty, lam(n(), elim(0, v(3), v(2), v(1), v(0)))),
        ),
    );
    let ty = pi(
        pi(n(), u(0)),
        pi(
            app(v(0), z()),
            pi(
                pi(n(), pi(app(v(2), v(0)), app(v(3), s(v(1))))),
                pi(n(), app(v(3), v(0))),
            ),
        ),
    );
    let k = Kernel::default();
    k.check(&term, &ty).unwrap();
    assert_eq!(k.normalize(&term).unwrap(), term);
}
#[test]
fn rejects_wrong_motive_domain_codomain_level_and_relevance() {
    let k = Kernel::default();
    for motive in [
        n(),
        lam(u(0), n()),
        lam(n(), z()),
        lam(n(), u(0)),
        T::Lam {
            relevance: deppy_core::Relevance::Erased,
            domain: n(),
            body: n(),
        }
        .arc(),
    ] {
        assert!(k
            .infer(&elim(0, motive, z(), lam(n(), lam(n(), z())), z()))
            .is_err());
    }
    assert_eq!(
        k.infer(&elim(
            u32::MAX,
            lam(n(), n()),
            z(),
            lam(n(), lam(n(), z())),
            z()
        )),
        Err(Error::UniverseOverflow)
    );
}
#[test]
fn rejects_invalid_branches_even_when_they_would_not_execute() {
    let k = Kernel::default();
    assert!(k
        .normalize(&elim(
            0,
            lam(n(), n()),
            n(),
            lam(n(), lam(n(), z())),
            s(z())
        ))
        .is_err());
    for step in [
        z(),
        lam(n(), z()),
        lam(n(), lam(n(), n())),
        lam(n(), lam(u(0), z())),
    ] {
        assert!(k
            .normalize(&elim(0, lam(n(), n()), z(), step, z()))
            .is_err());
    }
}
#[test]
fn rejects_wrong_dependent_induction_hypothesis() {
    let wrong = lam(n(), lam(n(), lam(n(), v(0))));
    assert!(Kernel::default()
        .infer(&elim(0, family(), z(), wrong, z()))
        .is_err());
}
#[test]
fn rejects_non_nat_scrutinee_and_exhausted_budget() {
    assert!(Kernel::default().normalize(&copy(n())).is_err());
    assert_eq!(
        Kernel::new(20).normalize(&copy(s(s(z())))),
        Err(Error::BudgetExceeded)
    );
}
