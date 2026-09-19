mod support;
use deppy_core::{Error, Kernel, Term};
use support::*;
fn vm() -> deppy_core::Tm {
    lam(n(), lam(vec(n(), v(0)), n()))
}
fn vs(body: deppy_core::Tm) -> deppy_core::Tm {
    lam(n(), lam(n(), lam(vec(n(), v(1)), lam(n(), body))))
}
fn fm() -> deppy_core::Tm {
    lam(n(), lam(fin(v(0)), n()))
}
fn fstep(body: deppy_core::Tm) -> deppy_core::Tm {
    lam(n(), lam(fin(v(0)), lam(n(), body)))
}
#[test]
fn vector_iota_uses_tail_induction_hypothesis() {
    let k = Kernel::default();
    let two = cons(n(), s(z()), s(z()), cons(n(), z(), z(), nil(n())));
    let fold = ve(0, n(), vm(), z(), vs(s(v(0))), s(s(z())), two);
    assert_eq!(k.normalize(&fold).unwrap(), s(s(z())));
    assert_eq!(
        k.normalize(&ve(0, n(), vm(), s(z()), vs(s(v(0))), z(), nil(n())))
            .unwrap(),
        s(z())
    );
}
#[test]
fn vector_step_receives_witness_head_and_original_tail() {
    let xs = cons(n(), s(z()), s(s(s(z()))), cons(n(), z(), s(z()), nil(n())));
    let k = Kernel::default();
    for (body, expected) in [(v(3), s(z())), (v(2), s(s(s(z()))))] {
        assert_eq!(
            k.normalize(&ve(0, n(), vm(), z(), vs(body), s(s(z())), xs.clone()))
                .unwrap(),
            expected
        );
    }
    let motive = lam(n(), lam(vec(n(), v(0)), vec(n(), v(1))));
    let step = lam(
        n(),
        lam(
            n(),
            lam(
                vec(n(), v(1)),
                lam(vec(n(), v(2)), cons(n(), v(3), v(2), v(1))),
            ),
        ),
    );
    assert_eq!(
        k.normalize(&ve(0, n(), motive, nil(n()), step, s(s(z())), xs.clone()))
            .unwrap(),
        xs
    );
}
#[test]
fn vector_motive_depends_on_index_and_scrutinee() {
    let motive = lam(n(), lam(vec(n(), v(0)), eq(vec(n(), v(1)), v(0), v(0))));
    let step = lam(
        n(),
        lam(
            n(),
            lam(
                vec(n(), v(1)),
                lam(
                    eq(vec(n(), v(2)), v(0), v(0)),
                    refl(vec(n(), s(v(3))), cons(n(), v(3), v(2), v(1))),
                ),
            ),
        ),
    );
    let xs = cons(n(), z(), s(z()), nil(n()));
    let term = ve(
        0,
        n(),
        motive,
        refl(vec(n(), z()), nil(n())),
        step,
        s(z()),
        xs.clone(),
    );
    assert_eq!(
        Kernel::default().normalize(&term).unwrap(),
        refl(vec(n(), s(z())), xs)
    );
}
#[test]
fn finite_iota_uses_predecessor_bound_and_hypothesis() {
    let k = Kernel::default();
    let i = fs(s(s(z())), fs(s(z()), fz(z())));
    assert_eq!(
        k.normalize(&fe(
            0,
            fm(),
            lam(n(), z()),
            fstep(s(v(0))),
            s(s(s(z()))),
            i.clone()
        ))
        .unwrap(),
        s(s(z()))
    );
    assert_eq!(
        k.normalize(&fe(0, fm(), lam(n(), v(0)), fstep(v(2)), s(s(s(z()))), i))
            .unwrap(),
        s(s(z()))
    );
    assert_eq!(
        k.normalize(&fe(
            0,
            fm(),
            lam(n(), v(0)),
            fstep(z()),
            s(s(z())),
            fz(s(z()))
        ))
        .unwrap(),
        s(z())
    );
}
#[test]
fn finite_motive_depends_on_bound_and_scrutinee() {
    let motive = lam(n(), lam(fin(v(0)), eq(fin(v(1)), v(0), v(0))));
    let zero = lam(n(), refl(fin(s(v(0))), fz(v(0))));
    let step = lam(
        n(),
        lam(
            fin(v(0)),
            lam(
                eq(fin(v(1)), v(0), v(0)),
                refl(fin(s(v(2))), fs(v(2), v(1))),
            ),
        ),
    );
    let i = fs(s(z()), fz(z()));
    let term = fe(0, motive, zero, step, s(s(z())), i.clone());
    assert_eq!(
        Kernel::default().normalize(&term).unwrap(),
        refl(fin(s(s(z()))), i)
    );
}
#[test]
fn eliminators_remain_neutral_under_symbolic_indices() {
    let k = Kernel::default();
    for term in [
        lam(
            n(),
            lam(
                vec(n(), v(0)),
                ve(0, n(), vm(), z(), vs(s(v(0))), v(1), v(0)),
            ),
        ),
        lam(
            n(),
            lam(
                fin(v(0)),
                fe(0, fm(), lam(n(), z()), fstep(s(v(0))), v(1), v(0)),
            ),
        ),
    ] {
        assert_eq!(k.normalize(&term).unwrap(), term);
        assert!(k
            .equivalent(&term, &term, &k.infer(&term).unwrap())
            .unwrap());
    }
    // Stuck eliminators retain their branches for conversion.
    let a = lam(vec(n(), z()), ve(0, n(), vm(), z(), vs(z()), z(), v(0)));
    let b = lam(vec(n(), z()), ve(0, n(), vm(), s(z()), vs(z()), z(), v(0)));
    assert!(!k.equivalent(&a, &b, &pi(vec(n(), z()), n())).unwrap());
}
#[test]
fn vector_carrier_and_motive_survive_outer_binders() {
    // A, P : (n : Nat) -> Vec A n -> Type0, nil branch, cons branch, n, xs.
    let pty = pi(n(), pi(vec(v(1), v(0)), u(0)));
    let base = app(app(v(0), z()), nil(v(1)));
    // A P d k h t ih
    let step = pi(
        n(),
        pi(
            v(3),
            pi(
                vec(v(4), v(1)),
                pi(
                    app(app(v(4), v(2)), v(0)),
                    app(app(v(5), s(v(3))), cons(v(6), v(3), v(2), v(1))),
                ),
            ),
        ),
    );
    let term = lam(
        u(0),
        lam(
            pty,
            lam(
                base,
                lam(
                    step,
                    lam(
                        n(),
                        lam(vec(v(4), v(0)), ve(0, v(5), v(4), v(3), v(2), v(1), v(0))),
                    ),
                ),
            ),
        ),
    );
    assert_eq!(Kernel::default().normalize(&term).unwrap(), term);
}
#[test]
fn rejects_bad_vec_eliminator_fields_before_iota() {
    let good = ve(0, n(), vm(), z(), vs(s(v(0))), z(), nil(n()));
    let Term::Data { arguments, .. } = good.as_ref() else {
        panic!()
    };
    let [ty, len, motive, base, cons, scrutinee] = arguments.as_slice() else {
        panic!()
    };
    for index in 0..7 {
        let mut fields = [
            ty.clone(),
            motive.clone(),
            base.clone(),
            cons.clone(),
            len.clone(),
            scrutinee.clone(),
        ];
        let level = if index == 6 {
            1
        } else {
            fields[index] = u(0);
            0
        };
        let [ty, motive, nil, cons, len, scrutinee] = fields;
        assert!(
            Kernel::default()
                .normalize(&ve(level, ty, motive, nil, cons, len, scrutinee))
                .is_err(),
            "{index}"
        );
    }
    assert!(Kernel::default()
        .infer(&ve(0, n(), vm(), z(), vs(z()), s(z()), nil(n())))
        .is_err());
    let wrong_ih = lam(n(), lam(n(), lam(vec(n(), v(1)), lam(fin(z()), z()))));
    assert!(Kernel::default()
        .infer(&ve(0, n(), vm(), z(), wrong_ih, z(), nil(n())))
        .is_err());
}
#[test]
fn rejects_bad_fin_eliminator_fields_before_iota() {
    let good = fe(0, fm(), lam(n(), z()), fstep(s(v(0))), s(z()), fz(z()));
    let Term::Data { arguments, .. } = good.as_ref() else {
        panic!()
    };
    let [bound, motive, zero, step, scrutinee] = arguments.as_slice() else {
        panic!()
    };
    for index in 0..6 {
        let mut fields = [
            motive.clone(),
            zero.clone(),
            step.clone(),
            bound.clone(),
            scrutinee.clone(),
        ];
        let level = if index == 5 {
            1
        } else {
            fields[index] = u(0);
            0
        };
        let [motive, zero, step, bound, scrutinee] = fields;
        assert!(
            Kernel::default()
                .normalize(&fe(level, motive, zero, step, bound, scrutinee))
                .is_err(),
            "{index}"
        );
    }
    assert!(Kernel::default()
        .infer(&fe(0, fm(), lam(n(), z()), fstep(z()), z(), fz(z())))
        .is_err());
    let wrong_ih = lam(n(), lam(fin(v(0)), lam(fin(z()), z())));
    assert!(Kernel::default()
        .infer(&fe(0, fm(), lam(n(), z()), wrong_ih, s(z()), fz(z())))
        .is_err());
}
#[test]
fn empty_fin_elimination_is_neutral_and_requires_fin_zero() {
    let k = Kernel::default();
    for term in [
        lam(fin(z()), absurd(n(), v(0))),
        lam(fin(z()), absurd(eq(fin(z()), v(0), v(0)), v(0))),
        lam(fin(z()), absurd(u(1), v(0))),
    ] {
        assert_eq!(k.normalize(&term).unwrap(), term);
        assert!(k
            .equivalent(&term, &term, &k.infer(&term).unwrap())
            .unwrap());
    }
    for bad in [
        absurd(n(), fz(z())),
        absurd(n(), z()),
        lam(fin(z()), absurd(z(), v(0))),
    ] {
        assert!(k.normalize(&bad).is_err());
    }
}
#[test]
fn eliminators_support_higher_result_universes() {
    let k = Kernel::default();
    let vm = lam(n(), lam(vec(n(), v(0)), u(0)));
    let vs = lam(n(), lam(n(), lam(vec(n(), v(1)), lam(u(0), n()))));
    assert_eq!(
        k.normalize(&ve(1, n(), vm, n(), vs, z(), nil(n())))
            .unwrap(),
        n()
    );
    let fm = lam(n(), lam(fin(v(0)), u(0)));
    let fs = lam(n(), lam(fin(v(0)), lam(u(0), n())));
    assert_eq!(
        k.normalize(&fe(1, fm, lam(n(), n()), fs, s(z()), fz(z())))
            .unwrap(),
        n()
    );
}
#[test]
fn eliminators_respect_budget_and_overflow() {
    for level in [0, u32::MAX] {
        let k = if level == 0 {
            Kernel::new(1)
        } else {
            Kernel::default()
        };
        let expected = if level == 0 {
            Error::BudgetExceeded
        } else {
            Error::UniverseOverflow
        };
        assert_eq!(
            k.infer(&ve(level, n(), vm(), z(), vs(z()), z(), nil(n()))),
            Err(expected.clone())
        );
        assert_eq!(
            k.infer(&fe(level, fm(), lam(n(), z()), fstep(z()), s(z()), fz(z()))),
            Err(expected)
        );
    }
}
