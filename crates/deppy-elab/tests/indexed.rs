use deppy_core::{Kernel, Term as C};
use deppy_elab::{
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn name(s: &str) -> E {
    E::name(s)
}
fn lam(s: &str, ty: E, body: E) -> E {
    E::lam(s, Explicit, Some(ty), body)
}
fn inferred(names: &[&str], mut body: E) -> E {
    for n in names.iter().rev() {
        body = E::lam(*n, Explicit, None, body);
    }
    body
}
fn singleton() -> E {
    E::vcons(E::Nat, E::Zero, E::Zero.succ(), E::vnil(E::Nat))
}
fn vm() -> E {
    inferred(&["k", "xs"], E::Nat)
}
fn fm() -> E {
    inferred(&["k", "i"], E::Nat)
}
fn vstep() -> E {
    inferred(&["k", "h", "t", "ih"], name("ih").succ())
}
fn fstep() -> E {
    inferred(&["k", "i", "ih"], name("ih").succ())
}
#[test]
fn explicit_indexed_constructors_and_universes() {
    let elab = Elaborator::default();
    for (term, ty) in [
        (E::vnil(E::Nat), E::vec(E::Nat, E::Zero)),
        (singleton(), E::vec(E::Nat, E::Zero.succ())),
        (E::fz(E::Zero), E::fin(E::Zero.succ())),
        (
            E::fs(E::Zero.succ(), E::fz(E::Zero)),
            E::fin(E::Zero.succ().succ()),
        ),
    ] {
        elab.check(&term, &ty).unwrap();
    }
    assert_eq!(
        elab.infer(&E::vec(E::Universe(0), E::Zero)).unwrap().ty,
        C::Universe(1).arc()
    );
}
#[test]
fn rejects_mismatched_constructor_witnesses() {
    let elab = Elaborator::default();
    for bad in [
        E::vcons(E::Nat, E::Zero.succ(), E::Zero, E::vnil(E::Nat)),
        E::vcons(E::Nat, E::Zero, E::Nat, E::vnil(E::Nat)),
        E::vnil(E::Zero),
        E::vec(E::Nat, E::Nat),
        E::fz(E::Nat),
        E::fs(E::Zero, E::fz(E::Zero)),
        E::fin(E::Nat),
    ] {
        assert!(elab.infer(&bad).is_err());
    }
    assert!(elab.check(&E::fz(E::Zero), &E::fin(E::Zero)).is_err());
}
#[test]
fn infers_implicit_carrier_and_length_from_vector() {
    let identity = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "n",
            Implicit,
            Some(E::Nat),
            lam("xs", E::vec(name("A"), name("n")), name("xs")),
        ),
    );
    let elab = Elaborator::default();
    let out = elab.infer(&identity.app(singleton())).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        elab.infer(&singleton()).unwrap().term
    );
}
#[test]
fn infers_bound_from_fin_and_constrains_constructor_holes() {
    let identity = E::lam(
        "n",
        Implicit,
        Some(E::Nat),
        lam("i", E::fin(name("n")), name("i")),
    );
    let elab = Elaborator::default();
    let out = elab.infer(&identity.app(E::fz(E::Zero))).unwrap();
    assert_eq!(
        out.ty,
        C::Fin {
            bound: C::Succ(C::Zero.arc()).arc()
        }
        .arc()
    );
    elab.check(&E::fz(E::Hole), &E::fin(E::Zero.succ()))
        .unwrap();
    elab.infer(&E::vcons(E::Nat, E::Hole, E::Zero, E::vnil(E::Nat)))
        .unwrap();
}
#[test]
fn elaborates_unannotated_branches_and_computes_iota() {
    let elab = Elaborator::default();
    let vec = E::vec_elim(
        0,
        E::Nat,
        vm(),
        E::Zero,
        vstep(),
        E::Zero.succ(),
        singleton(),
    );
    let fin = E::fin_elim(
        0,
        fm(),
        inferred(&["k"], E::Zero),
        fstep(),
        E::Zero.succ().succ(),
        E::fs(E::Zero.succ(), E::fz(E::Zero)),
    );
    for term in [vec, fin] {
        let out = elab.infer(&term).unwrap();
        assert_eq!(
            Kernel::default().normalize(&out.term).unwrap(),
            C::Succ(C::Zero.arc()).arc()
        );
    }
}
#[test]
fn vector_motive_depends_on_both_binders() {
    let motive = inferred(
        &["k", "xs"],
        E::eq(E::vec(E::Nat, name("k")), name("xs"), name("xs")),
    );
    let base = E::vnil(E::Nat).refl();
    let step = inferred(
        &["k", "h", "t", "ih"],
        E::vcons(E::Nat, name("k"), name("h"), name("t")).refl(),
    );
    let expr = E::vec_elim(0, E::Nat, motive, base, step, E::Zero.succ(), singleton());
    let out = Elaborator::default().infer(&expr).unwrap();
    let expected = Elaborator::default().infer(&singleton().refl()).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        expected.term
    );
}
#[test]
fn finite_motive_depends_on_both_binders() {
    let motive = inferred(&["k", "i"], E::eq(E::fin(name("k")), name("i"), name("i")));
    let base = inferred(&["k"], E::fz(name("k")).refl());
    let step = inferred(&["k", "i", "ih"], E::fs(name("k"), name("i")).refl());
    let i = E::fs(E::Zero.succ(), E::fz(E::Zero));
    let out = Elaborator::default()
        .infer(&E::fin_elim(
            0,
            motive,
            base,
            step,
            E::Zero.succ().succ(),
            i.clone(),
        ))
        .unwrap();
    let expected = Elaborator::default().infer(&i.refl()).unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        expected.term
    );
}
#[test]
fn polymorphic_vector_copy_preserves_scopes() {
    let motive = inferred(&["k", "xs"], E::vec(name("A"), name("k")));
    let step = inferred(
        &["k", "h", "t", "ih"],
        E::vcons(name("A"), name("k"), name("h"), name("ih")),
    );
    let term = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        lam(
            "n",
            E::Nat,
            lam(
                "xs",
                E::vec(name("A"), name("n")),
                E::vec_elim(
                    0,
                    name("A"),
                    motive,
                    E::vnil(name("A")),
                    step,
                    name("n"),
                    name("xs"),
                ),
            ),
        ),
    );
    let out = Elaborator::default().infer(&term).unwrap();
    let k = Kernel::default();
    k.check(&k.normalize(&out.term).unwrap(), &out.ty).unwrap();
    let applied = term.app(E::Zero.succ()).app(singleton());
    let out = Elaborator::default().infer(&applied).unwrap();
    assert_eq!(
        k.normalize(&out.term).unwrap(),
        Elaborator::default().infer(&singleton()).unwrap().term
    );
}
#[test]
fn type_level_indexed_elimination_reduces_in_annotations() {
    let vm = inferred(&["k", "xs"], E::Universe(0));
    let fm = inferred(&["k", "i"], E::Universe(0));
    let vty = E::vec_elim(
        1,
        E::Nat,
        vm,
        E::Nat,
        inferred(&["k", "h", "t", "ih"], E::Nat),
        E::Zero.succ(),
        singleton(),
    );
    let fty = E::fin_elim(
        1,
        fm,
        inferred(&["k"], E::Nat),
        inferred(&["k", "i", "ih"], E::Nat),
        E::Zero.succ(),
        E::fz(E::Zero),
    );
    for ty in [vty, fty] {
        Elaborator::default().check(&E::Zero, &ty).unwrap();
    }
}
#[test]
fn neutral_indexed_eliminators_unify_after_binder_renaming() {
    for (domain, body) in [
        (
            E::vec(E::Nat, E::Zero),
            E::vec_elim(0, E::Nat, vm(), E::Zero, vstep(), E::Zero, name("x")),
        ),
        (
            E::fin(E::Zero.succ()),
            E::fin_elim(
                0,
                fm(),
                inferred(&["k"], E::Zero),
                fstep(),
                E::Zero.succ(),
                name("x"),
            ),
        ),
        (E::fin(E::Zero), E::fin0_elim(E::Nat, name("x"))),
    ] {
        let f = lam("x", domain.clone(), body);
        let proof = lam("z", domain.clone(), f.clone().app(name("z")).refl());
        let ty = E::pi(
            "w",
            Explicit,
            domain,
            E::eq(E::Nat, f.clone().app(name("w")), f.app(name("w"))),
        );
        Elaborator::default().check(&proof, &ty).unwrap();
    }
}
#[test]
fn fin_zero_elimination_checks_dependent_target_and_rejects_inhabited_fin() {
    let term = lam(
        "i",
        E::fin(E::Zero),
        E::fin0_elim(E::eq(E::fin(E::Zero), name("i"), name("i")), name("i")),
    );
    let out = Elaborator::default().infer(&term).unwrap();
    Kernel::default().normalize(&out.term).unwrap();
    for bad in [
        E::fin0_elim(E::Nat, E::fz(E::Zero)),
        E::fin0_elim(E::Zero, E::Zero),
    ] {
        assert!(Elaborator::default().infer(&bad).is_err());
    }
}
#[test]
fn rejects_wrong_motives_induction_hypotheses_and_scrutinee_indices() {
    let elab = Elaborator::default();
    let wrong_vstep = inferred(&["k", "h", "t"], lam("ih", E::fin(E::Zero), E::Zero));
    let wrong_fstep = inferred(&["k", "i"], lam("ih", E::fin(E::Zero), E::Zero));
    for bad in [
        E::vec_elim(
            0,
            E::Nat,
            vm(),
            E::Zero,
            wrong_vstep,
            E::Zero,
            E::vnil(E::Nat),
        ),
        E::fin_elim(
            0,
            fm(),
            inferred(&["k"], E::Zero),
            wrong_fstep,
            E::Zero.succ(),
            E::fz(E::Zero),
        ),
        E::vec_elim(0, E::Nat, vm(), E::Zero, vstep(), E::Zero, singleton()),
        E::fin_elim(
            0,
            fm(),
            inferred(&["k"], E::Zero),
            fstep(),
            E::Zero,
            E::fz(E::Zero),
        ),
        E::vec_elim(
            0,
            E::Nat,
            lam("k", E::Nat, lam("i", E::fin(name("k")), E::Nat)),
            E::Zero,
            vstep(),
            E::Zero,
            E::vnil(E::Nat),
        ),
    ] {
        assert!(elab.infer(&bad).is_err());
    }
}
#[test]
fn unused_branches_still_require_valid_terms_and_solved_holes() {
    let elab = Elaborator::default();
    for step in [E::Nat, E::Hole] {
        assert!(elab
            .infer(&E::vec_elim(
                0,
                E::Nat,
                vm(),
                E::Zero,
                step.clone(),
                E::Zero,
                E::vnil(E::Nat)
            ))
            .is_err());
        assert!(elab
            .infer(&E::fin_elim(
                0,
                fm(),
                inferred(&["k"], E::Zero),
                step,
                E::Zero.succ(),
                E::fz(E::Zero)
            ))
            .is_err());
    }
}
#[test]
fn indexed_elaboration_respects_universes_and_budget() {
    for level in [1, u32::MAX] {
        assert!(Elaborator::default()
            .infer(&E::vec_elim(
                level,
                E::Nat,
                vm(),
                E::Zero,
                vstep(),
                E::Zero,
                E::vnil(E::Nat)
            ))
            .is_err());
        assert!(Elaborator::default()
            .infer(&E::fin_elim(
                level,
                fm(),
                inferred(&["k"], E::Zero),
                fstep(),
                E::Zero.succ(),
                E::fz(E::Zero)
            ))
            .is_err());
    }
    assert!(matches!(
        Elaborator::new(1).infer(&E::fz(E::Zero)),
        Err(Error::BudgetExceeded)
    ));
}
