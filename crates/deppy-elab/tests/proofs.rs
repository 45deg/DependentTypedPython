use deppy_core::{Kernel, Term as C};
use deppy_elab::{
    prelude::{cong, nat_add, transport, zero_right},
    Elaborator, Expr as E,
    Plicity::Explicit,
};
fn name(s: &str) -> E {
    E::name(s)
}
fn lam(s: &str, a: E, b: E) -> E {
    E::lam(s, Explicit, Some(a), b)
}
fn numeral(n: usize) -> E {
    (0..n).fold(E::Zero, |x, _| x.succ())
}
fn theorem() -> E {
    E::pi(
        "n",
        Explicit,
        E::Nat,
        E::eq(E::Nat, nat_add().app(name("n")).app(E::Zero), name("n")),
    )
}
#[test]
fn zero_right_proves_the_symbolic_theorem() {
    let out = Elaborator::default()
        .check(&zero_right(), &theorem())
        .unwrap();
    Kernel::default().check(&out.term, &out.ty).unwrap();
}
#[test]
fn zero_right_computes_to_reflexivity_on_numerals() {
    for n in 0..6 {
        let elab = Elaborator::default();
        let proof = elab.infer(&zero_right().app(numeral(n))).unwrap();
        let refl = elab.infer(&numeral(n).refl()).unwrap();
        assert_eq!(Kernel::default().normalize(&proof.term).unwrap(), refl.term);
    }
}
#[test]
fn rejects_refl_as_a_symbolic_zero_right_proof() {
    let false_proof = lam("n", E::Nat, name("n").refl());
    assert!(Elaborator::default()
        .check(&false_proof, &theorem())
        .is_err());
}
#[test]
fn derived_definitions_support_distinct_concrete_universes() {
    for (u, v) in [(0, 0), (0, 1), (1, 0), (1, 2)] {
        Elaborator::default().infer(&cong(u, v)).unwrap();
        Elaborator::default().infer(&transport(u, v)).unwrap();
    }
}
#[test]
fn congruence_infers_endpoints_and_computes_on_refl() {
    let out = Elaborator::default()
        .infer(
            &cong(0, 0)
                .app(lam("n", E::Nat, name("n").succ()))
                .app(E::Zero.refl()),
        )
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        C::Refl {
            ty: C::Nat.arc(),
            value: C::Succ(C::Zero.arc()).arc()
        }
        .arc()
    );
}
fn changing_family() -> E {
    // P Z = Nat, P (S k) = Nat -> Nat.
    lam(
        "n",
        E::Nat,
        E::nat_elim(
            1,
            lam("k", E::Nat, E::Universe(0)),
            E::Nat,
            lam(
                "k",
                E::Nat,
                lam("ih", E::Universe(0), E::pi("a", Explicit, E::Nat, E::Nat)),
            ),
            name("n"),
        ),
    )
}
#[test]
fn transport_checks_a_dependent_family_and_computes_on_refl() {
    let elab = Elaborator::default();
    let out = elab
        .infer(
            &transport(0, 0)
                .app(changing_family())
                .app(E::Zero.refl())
                .app(E::Zero),
        )
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        C::Zero.arc()
    );
    let id = lam("x", E::Nat, name("x"));
    let out = elab
        .infer(
            &transport(0, 0)
                .app(changing_family())
                .app(E::Zero.succ().refl())
                .app(id.clone()),
        )
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        elab.infer(&id).unwrap().term
    );
}
#[test]
fn neutral_transport_changes_type_and_retains_the_proof() {
    let proof_ty = E::eq(E::Nat, E::Zero, E::Zero.succ());
    let term = lam(
        "p",
        proof_ty.clone(),
        transport(0, 0)
            .app(changing_family())
            .app(name("p"))
            .app(E::Zero),
    );
    let ty = E::pi(
        "p",
        Explicit,
        proof_ty,
        E::pi("n", Explicit, E::Nat, E::Nat),
    );
    let out = Elaborator::default().check(&term, &ty).unwrap();
    let normal = Kernel::default().normalize(&out.term).unwrap();
    let C::Lam { body, .. } = normal.as_ref() else {
        panic!()
    };
    assert!(matches!(body.as_ref(),C::J {proof,..} if matches!(proof.as_ref(),C::Var(0))));
}
#[test]
fn transport_rejects_wrong_source_value() {
    let expr = transport(0, 0)
        .app(changing_family())
        .app(E::Zero.succ().refl())
        .app(E::Zero);
    assert!(Elaborator::default().infer(&expr).is_err());
}
#[test]
fn reflexivity_cannot_identify_arbitrary_proofs() {
    let eq = E::eq(E::Nat, E::Zero, E::Zero);
    let expr = lam("p", eq.clone(), lam("q", eq.clone(), name("p").refl()));
    let ty = E::pi(
        "p",
        Explicit,
        eq.clone(),
        E::pi("q", Explicit, eq.clone(), E::eq(eq, name("p"), name("q"))),
    );
    assert!(Elaborator::default().check(&expr, &ty).is_err());
}
