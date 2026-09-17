mod support;
use deppy_core::{Error, Kernel};
use support::*;
#[test]
fn indexed_families_and_constructor_types() {
    let k = Kernel::default();
    assert_eq!(k.infer(&vec(n(), z())).unwrap(), u(0));
    assert_eq!(k.infer(&vec(u(0), s(z()))).unwrap(), u(1));
    assert_eq!(k.infer(&fin(z())).unwrap(), u(0));
    assert_eq!(k.infer(&nil(n())).unwrap(), vec(n(), z()));
    assert_eq!(
        k.infer(&cons(n(), z(), z(), nil(n()))).unwrap(),
        vec(n(), s(z()))
    );
    assert_eq!(k.infer(&fz(z())).unwrap(), fin(s(z())));
    assert_eq!(k.infer(&fs(s(z()), fz(z()))).unwrap(), fin(s(s(z()))));
}
#[test]
fn rejects_bad_vec_carriers_lengths_heads_and_tails() {
    let k = Kernel::default();
    for bad in [
        vec(z(), z()),
        vec(n(), n()),
        nil(z()),
        cons(z(), z(), z(), nil(n())),
        cons(n(), n(), z(), nil(n())),
        cons(n(), z(), n(), nil(n())),
        cons(n(), s(z()), z(), nil(n())),
        cons(n(), z(), z(), nil(u(0))),
    ] {
        assert!(k.normalize(&bad).is_err(), "{bad:?}");
    }
}
#[test]
fn rejects_forged_finite_indices() {
    let k = Kernel::default();
    for bad in [
        fin(n()),
        fz(n()),
        fs(n(), fz(z())),
        fs(z(), fz(z())),
        fs(s(s(z())), fz(z())),
    ] {
        assert!(k.normalize(&bad).is_err(), "{bad:?}");
    }
    for term in [fz(z()), fs(s(z()), fz(z()))] {
        assert!(k.check(&term, &fin(z())).is_err());
    }
}
#[test]
fn indexed_types_obey_non_cumulative_universes() {
    let k = Kernel::default();
    assert!(k.check(&vec(n(), z()), &u(1)).is_err());
    assert!(k.check(&fin(s(z())), &u(1)).is_err());
    k.check(&nil(u(0)), &vec(u(0), z())).unwrap();
    assert!(k.check(&nil(n()), &vec(u(0), z())).is_err());
}
#[test]
fn annotations_and_witnesses_normalize_under_binders() {
    let term = lam(
        u(0),
        lam(
            n(),
            lam(v(1), lam(vec(v(2), v(1)), cons(v(3), v(2), v(1), v(0)))),
        ),
    );
    let k = Kernel::default();
    let ty = k.infer(&term).unwrap();
    assert_eq!(k.normalize(&term).unwrap(), term);
    assert!(k.equivalent(&term, &term, &ty).unwrap());
    let term = lam(n(), lam(fin(v(0)), fs(v(1), v(0))));
    assert_eq!(k.normalize(&term).unwrap(), term);
    let beta = app(lam(n(), v(0)), z());
    assert_eq!(k.normalize(&fz(beta.clone())).unwrap(), fz(z()));
    assert_eq!(
        k.normalize(&cons(n(), beta, z(), nil(n()))).unwrap(),
        cons(n(), z(), z(), nil(n()))
    );
}
#[test]
fn distinct_elements_and_indices_are_not_equal() {
    let k = Kernel::default();
    assert!(!k
        .equivalent(
            &cons(n(), z(), z(), nil(n())),
            &cons(n(), z(), s(z()), nil(n())),
            &vec(n(), s(z()))
        )
        .unwrap());
    assert!(!k
        .equivalent(&fz(s(z())), &fs(s(z()), fz(z())), &fin(s(s(z()))))
        .unwrap());
    assert!(!k
        .equivalent(&vec(n(), z()), &vec(n(), s(z())), &u(0))
        .unwrap());
    assert!(!k.equivalent(&fin(z()), &fin(s(z())), &u(0)).unwrap());
}
#[test]
fn indexed_constructors_respect_budget_and_overflow() {
    assert_eq!(Kernel::new(1).infer(&nil(n())), Err(Error::BudgetExceeded));
    assert_eq!(
        Kernel::default().infer(&vec(u(u32::MAX), z())),
        Err(Error::UniverseOverflow)
    );
}
