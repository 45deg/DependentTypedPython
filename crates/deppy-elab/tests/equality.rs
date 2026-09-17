use deppy_core::{Kernel, Term as C};
use deppy_elab::{
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn name(s: &str) -> E {
    E::name(s)
}
fn lam(s: &str, a: E, b: E) -> E {
    E::lam(s, Explicit, Some(a), b)
}
fn motive() -> E {
    E::lam("y", Explicit, None, E::lam("p", Explicit, None, E::Nat))
}
fn simple_j(base: E, right: E, proof: E) -> E {
    E::j(0, E::Nat, E::Zero, motive(), base, right, proof)
}
#[test]
fn refl_infers_carrier_and_checks_both_endpoints() {
    let elab = Elaborator::default();
    let out = elab.infer(&E::Zero.refl()).unwrap();
    assert_eq!(
        out.ty,
        C::Eq {
            ty: C::Nat.arc(),
            left: C::Zero.arc(),
            right: C::Zero.arc()
        }
        .arc()
    );
    assert!(elab
        .check(&E::Zero.refl(), &E::eq(E::Nat, E::Zero, E::Zero.succ()))
        .is_err());
    assert!(elab
        .check(&E::Zero.refl(), &E::eq(E::Nat, E::Zero.succ(), E::Zero))
        .is_err());
}
#[test]
fn expected_equality_supplies_lambda_annotation_and_solves_hole() {
    let elab = Elaborator::default();
    let id = lam("n", E::Nat, name("n"));
    let ty = E::eq(E::pi("n", Explicit, E::Nat, E::Nat), id.clone(), id);
    elab.check(&E::lam("x", Explicit, None, name("x")).refl(), &ty)
        .unwrap();
    elab.check(&E::Hole.refl(), &E::eq(E::Nat, E::Zero, E::Zero))
        .unwrap();
}
#[test]
fn implicit_carrier_and_endpoints_are_inferred_from_equality_proof() {
    let f = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "x",
            Implicit,
            Some(name("A")),
            E::lam(
                "y",
                Implicit,
                Some(name("A")),
                lam("p", E::eq(name("A"), name("x"), name("y")), name("y")),
            ),
        ),
    );
    let out = Elaborator::default().infer(&f.app(E::Zero.refl())).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        C::Zero.arc()
    );
}
#[test]
fn j_checks_annotation_free_motive_and_reduces_in_types() {
    let elab = Elaborator::default();
    let out = elab
        .infer(&simple_j(E::Zero.succ(), E::Zero, E::Zero.refl()))
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        C::Succ(C::Zero.arc()).arc()
    );
    let family = E::j(
        1,
        E::Nat,
        E::Zero,
        E::lam(
            "y",
            Explicit,
            None,
            E::lam("p", Explicit, None, E::Universe(0)),
        ),
        E::Nat,
        E::Zero,
        E::Zero.refl(),
    );
    elab.check(&E::Zero, &family).unwrap();
}
#[test]
fn j_result_can_depend_on_the_proof() {
    let motive = E::lam(
        "y",
        Explicit,
        None,
        E::lam(
            "p",
            Explicit,
            None,
            E::eq(E::eq(E::Nat, E::Zero, name("y")), name("p"), name("p")),
        ),
    );
    let term = E::j(
        0,
        E::Nat,
        E::Zero,
        motive,
        E::Zero.refl().refl(),
        E::Zero,
        E::Zero.refl(),
    );
    let out = Elaborator::default().infer(&term).unwrap();
    let expected = Elaborator::default().infer(&E::Zero.refl().refl()).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        expected.term
    );
}
#[test]
fn stuck_j_roundtrips_under_binders_and_unifies() {
    let a = lam(
        "q",
        E::eq(E::Nat, E::Zero, E::Zero),
        E::eq(
            E::Nat,
            simple_j(E::Zero, E::Zero, name("q")),
            simple_j(E::Zero, E::Zero, name("q")),
        ),
    );
    let proof = lam(
        "p",
        E::eq(E::Nat, E::Zero, E::Zero),
        simple_j(E::Zero, E::Zero, name("p")).refl(),
    );
    let ty = E::pi(
        "r",
        Explicit,
        E::eq(E::Nat, E::Zero, E::Zero),
        a.app(name("r")),
    );
    let out = Elaborator::default().check(&proof, &ty).unwrap();
    let normalized = Kernel::default().normalize(&out.term).unwrap();
    Kernel::default().check(&normalized, &out.ty).unwrap();
}
#[test]
fn rejects_bad_j_arguments_and_k_shaped_motive() {
    let elab = Elaborator::default();
    for bad in [
        simple_j(E::Nat, E::Zero, E::Zero.refl()),
        simple_j(E::Zero, E::Zero.succ(), E::Zero.refl()),
        simple_j(E::Zero, E::Zero, E::Zero),
    ] {
        assert!(elab.infer(&bad).is_err());
    }
    let fixed = lam(
        "y",
        E::Nat,
        lam("p", E::eq(E::Nat, E::Zero, E::Zero), E::Nat),
    );
    assert!(elab
        .infer(&E::j(
            0,
            E::Nat,
            E::Zero,
            fixed,
            E::Zero,
            E::Zero,
            E::Zero.refl()
        ))
        .is_err());
    assert!(elab.infer(&E::eq(E::Nat, E::Nat, E::Zero)).is_err());
}
#[test]
fn unused_j_holes_are_not_erased() {
    assert!(matches!(
        Elaborator::default().infer(&simple_j(E::Hole, E::Zero, E::Zero.refl())),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn no_equality_reflection_in_elaboration() {
    let proof = lam(
        "x",
        E::Nat,
        lam(
            "y",
            E::Nat,
            lam("p", E::eq(E::Nat, name("x"), name("y")), name("x").refl()),
        ),
    );
    let ty = E::pi(
        "x",
        Explicit,
        E::Nat,
        E::pi(
            "y",
            Explicit,
            E::Nat,
            E::pi(
                "p",
                Explicit,
                E::eq(E::Nat, name("x"), name("y")),
                E::eq(E::Nat, name("x"), name("y")),
            ),
        ),
    );
    assert!(Elaborator::default().check(&proof, &ty).is_err());
}
#[test]
fn rejects_wrong_universe_overflow_and_budget() {
    let elab = Elaborator::default();
    for level in [1, u32::MAX] {
        assert!(elab
            .infer(&E::j(
                level,
                E::Nat,
                E::Zero,
                motive(),
                E::Zero,
                E::Zero,
                E::Zero.refl()
            ))
            .is_err());
    }
    assert!(matches!(
        Elaborator::new(1).infer(&E::Zero.refl()),
        Err(Error::BudgetExceeded)
    ));
}
