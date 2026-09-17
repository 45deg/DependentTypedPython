use deppy_core::{Kernel, Term};
use deppy_elab::{
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(s: &str) -> E {
    E::name(s)
}
fn ty() -> E {
    E::sigma("k", E::Nat, E::vec(E::Nat, n("k")))
}
fn packed() -> E {
    E::pair(E::Zero, E::vnil(E::Nat)).ann(ty())
}
fn lam(name: &str, ty: E, body: E) -> E {
    E::lam(name, Explicit, Some(ty), body)
}
#[test]
fn expected_sigma_checks_pair_and_computes_projections() {
    let e = Elaborator::default();
    let k = Kernel::default();
    e.check(&E::pair(E::Zero, E::vnil(E::Nat)), &ty()).unwrap();
    assert_eq!(
        k.normalize(&e.infer(&packed().fst()).unwrap().term)
            .unwrap(),
        Term::Zero.arc()
    );
    let out = e.infer(&packed().snd()).unwrap();
    assert_eq!(
        k.normalize(&out.ty).unwrap(),
        e.infer(&E::vec(E::Nat, E::Zero)).unwrap().term
    );
    assert_eq!(
        k.normalize(&out.term).unwrap(),
        e.infer(&E::vnil(E::Nat)).unwrap().term
    );
}
#[test]
fn second_projection_has_dependent_type_under_binders() {
    let e = Elaborator::default();
    let f = lam("p", ty(), n("p").snd());
    e.check(
        &f,
        &E::pi("p", Explicit, ty(), E::vec(E::Nat, n("p").fst())),
    )
    .unwrap();
}
#[test]
fn pair_requires_expected_type_and_rejects_mismatches() {
    let e = Elaborator::default();
    assert_eq!(
        e.infer(&E::pair(E::Zero, E::Zero)).unwrap_err(),
        Error::AnnotationRequired
    );
    for p in [
        E::pair(E::Nat, E::vnil(E::Nat)),
        E::pair(E::Zero.succ(), E::vnil(E::Nat)),
        E::pair(E::Zero, E::Zero),
    ] {
        assert!(e.check(&p, &ty()).is_err());
    }
    assert!(e.check(&E::pair(E::Zero, E::Zero), &E::Nat).is_err());
    assert!(e.infer(&E::Zero.fst()).is_err());
    assert!(e.infer(&E::Nat.snd()).is_err());
    assert!(e.infer(&E::sigma("x", E::Nat, E::Zero)).is_err());
}
#[test]
fn first_component_hole_can_be_solved_by_second_component() {
    let e = Elaborator::default();
    let out = e.check(&E::pair(E::Hole, E::vnil(E::Nat)), &ty()).unwrap();
    assert_eq!(
        Kernel::default()
            .normalize(&Term::Fst(out.term).arc())
            .unwrap(),
        Term::Zero.arc()
    );
    assert!(matches!(
        e.check(&E::pair(E::Hole, E::Hole), &ty()),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn implicit_carrier_is_inferred_through_sigma() {
    let e = Elaborator::default();
    let f = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        lam(
            "p",
            E::sigma("k", E::Nat, E::vec(n("A"), n("k"))),
            n("p").snd(),
        ),
    );
    let out = e.infer(&f.app(packed())).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        e.infer(&E::vnil(E::Nat)).unwrap().term
    );
}
#[test]
fn nested_sigma_scope_and_shadowing() {
    let e = Elaborator::default();
    let ty = E::sigma(
        "A",
        E::Universe(0),
        E::sigma("x", n("A"), E::eq(n("A"), n("x"), n("x"))),
    );
    e.check(&E::pair(E::Nat, E::pair(E::Zero, E::Zero.refl())), &ty)
        .unwrap();
    let ty = E::pi(
        "A",
        Explicit,
        E::Universe(0),
        E::pi(
            "x",
            Explicit,
            n("A"),
            E::sigma("A", n("A"), E::eq(n("A"), n("x"), n("x"))),
        ),
    );
    // The inner A is a value, and cannot be used as an equality carrier.
    assert!(e.infer(&ty).is_err());
}
#[test]
fn sigma_universes_and_alpha_equivalence() {
    let e = Elaborator::default();
    let a = E::sigma("A", E::Universe(0), n("A"));
    let b = E::sigma("B", E::Universe(0), n("B"));
    e.check(&E::pair(E::Nat, E::Zero).ann(a.clone()), &b)
        .unwrap();
    assert_eq!(e.infer(&a).unwrap().ty, Term::Universe(1).arc());
    assert!(e.check(&a, &E::Universe(2)).is_err());
    assert!(e
        .infer(&E::sigma("x", E::Universe(u32::MAX), E::Nat))
        .is_err());
}
#[test]
fn neutral_projections_unify_and_function_eta_still_works() {
    let e = Elaborator::default();
    let pair_ty = E::sigma("f", E::pi("x", Explicit, E::Nat, E::Nat), E::Nat);
    let f = lam(
        "p",
        pair_ty,
        E::pair(n("p").fst(), n("p").snd()).ann(E::sigma(
            "g",
            E::pi("y", Explicit, E::Nat, E::Nat),
            E::Nat,
        )),
    );
    e.infer(&f).unwrap();
    let fun = E::pi("x", Explicit, E::Nat, E::Nat);
    let pair_ty = E::sigma("f", fun.clone(), fun.clone());
    for proj in [n("p").fst(), n("p").snd()] {
        let proof = lam(
            "p",
            pair_ty.clone(),
            proj.clone().refl().ann(E::eq(
                fun.clone(),
                proj.clone(),
                lam("x", E::Nat, proj.app(n("x"))),
            )),
        );
        e.infer(&proof).unwrap();
    }
}
#[test]
fn rejects_sigma_eta_and_invalid_discarded_components() {
    let e = Elaborator::default();
    let proof = lam(
        "p",
        ty(),
        n("p")
            .refl()
            .ann(E::eq(ty(), n("p"), E::pair(n("p").fst(), n("p").snd()))),
    );
    assert!(e.infer(&proof).is_err());
    assert!(e
        .infer(
            &E::pair(E::Zero, E::Nat)
                .ann(E::sigma("x", E::Nat, E::Nat))
                .fst()
        )
        .is_err());
    assert!(e
        .infer(
            &E::pair(E::Zero, E::Hole)
                .ann(E::sigma("x", E::Nat, E::Nat))
                .fst()
        )
        .is_err());
}
