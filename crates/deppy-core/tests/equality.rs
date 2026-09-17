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
fn eq(a: Tm, x: Tm, y: Tm) -> Tm {
    T::Eq {
        ty: a,
        left: x,
        right: y,
    }
    .arc()
}
fn refl(a: Tm, x: Tm) -> Tm {
    T::Refl { ty: a, value: x }.arc()
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
fn constant_motive() -> Tm {
    lam(n(), lam(eq(n(), z(), v(0)), n()))
}
fn j(motive: Tm, base: Tm, right: Tm, proof: Tm) -> Tm {
    T::J {
        level: 0,
        ty: n(),
        left: z(),
        motive,
        base,
        right,
        proof,
    }
    .arc()
}
#[test]
fn equality_universe_and_reflexivity() {
    let k = Kernel::default();
    assert_eq!(k.infer(&eq(n(), z(), z())).unwrap(), T::Universe(0).arc());
    assert_eq!(
        k.infer(&eq(T::Universe(0).arc(), n(), n())).unwrap(),
        T::Universe(1).arc()
    );
    k.check(&refl(n(), z()), &eq(n(), z(), z())).unwrap();
    assert!(k.check(&eq(n(), z(), z()), &T::Universe(1).arc()).is_err());
}
#[test]
fn rejects_bad_carrier_endpoints_and_reflexivity() {
    let k = Kernel::default();
    for term in [
        eq(z(), z(), z()),
        eq(n(), n(), z()),
        eq(n(), z(), n()),
        refl(z(), z()),
        refl(n(), n()),
    ] {
        assert!(k.normalize(&term).is_err());
    }
    assert!(k
        .check(&refl(n(), z()), &eq(n(), z(), T::Succ(z()).arc()))
        .is_err());
}
#[test]
fn j_computes_only_on_reflexivity() {
    let k = Kernel::default();
    assert_eq!(
        k.normalize(&j(
            constant_motive(),
            T::Succ(z()).arc(),
            z(),
            refl(n(), z())
        ))
        .unwrap(),
        T::Succ(z()).arc()
    );
    let stuck = lam(eq(n(), z(), z()), j(constant_motive(), z(), z(), v(0)));
    assert_eq!(k.normalize(&stuck).unwrap(), stuck);
    assert!(!k
        .equivalent(
            &stuck,
            &lam(eq(n(), z(), z()), z()),
            &pi(eq(n(), z(), z()), n())
        )
        .unwrap());
}
#[test]
fn motive_can_depend_on_the_proof() {
    // C y p = Eq (Eq Nat Z y) p p.
    let motive = lam(
        n(),
        lam(eq(n(), z(), v(0)), eq(eq(n(), z(), v(1)), v(0), v(0))),
    );
    let base = refl(eq(n(), z(), z()), refl(n(), z()));
    let term = j(motive, base.clone(), z(), refl(n(), z()));
    Kernel::default()
        .check(
            &term,
            &eq(eq(n(), z(), z()), refl(n(), z()), refl(n(), z())),
        )
        .unwrap();
    assert_eq!(Kernel::default().normalize(&term).unwrap(), base);
}
#[test]
fn neutral_j_preserves_surrounding_binders_and_result_type() {
    // A, x, y, p; C y q = Eq A x y, d = refl x.
    let motive = lam(v(3), lam(eq(v(4), v(3), v(0)), eq(v(5), v(4), v(1))));
    let body = T::J {
        level: 0,
        ty: v(3),
        left: v(2),
        motive,
        base: refl(v(3), v(2)),
        right: v(1),
        proof: v(0),
    }
    .arc();
    let term = lam(
        T::Universe(0).arc(),
        lam(v(0), lam(v(1), lam(eq(v(2), v(1), v(0)), body))),
    );
    let k = Kernel::default();
    let ty = k.infer(&term).unwrap();
    assert_eq!(k.normalize(&term).unwrap(), term);
    assert!(k.equivalent(&term, &term, &ty).unwrap());
}
#[test]
fn rejects_bad_j_inputs_even_when_refl_would_discard_them() {
    let good = j(constant_motive(), z(), z(), refl(n(), z()));
    let T::J {
        level,
        ty,
        left,
        motive,
        base,
        right,
        proof,
    } = good.as_ref()
    else {
        panic!()
    };
    for field in 0..7 {
        let mut parts = [
            ty.clone(),
            left.clone(),
            motive.clone(),
            base.clone(),
            right.clone(),
            proof.clone(),
        ];
        let mut l = *level;
        if field == 6 {
            l = 1;
        } else {
            parts[field] = T::Universe(0).arc();
        }
        let [ty, left, motive, base, right, proof] = parts;
        assert!(
            Kernel::default()
                .normalize(
                    &T::J {
                        level: l,
                        ty,
                        left,
                        motive,
                        base,
                        right,
                        proof
                    }
                    .arc()
                )
                .is_err(),
            "field {field}"
        );
    }
}
#[test]
fn rejects_wrong_endpoint_proof_and_fixed_endpoint_motive() {
    let k = Kernel::default();
    assert!(k
        .infer(&j(
            constant_motive(),
            z(),
            T::Succ(z()).arc(),
            refl(n(), z())
        ))
        .is_err());
    // A K-shaped motive fixes the right endpoint to Z instead of binding y.
    let fixed = lam(n(), lam(eq(n(), z(), z()), n()));
    assert!(k.infer(&j(fixed, z(), z(), refl(n(), z()))).is_err());
}
#[test]
fn equality_proofs_do_not_enable_reflection_or_proof_irrelevance() {
    let k = Kernel::default();
    // Even with p : Eq Nat x y in scope, refl x cannot prove Eq Nat x y.
    let term = lam(n(), lam(n(), lam(eq(n(), v(1), v(0)), refl(n(), v(2)))));
    let ty = pi(n(), pi(n(), pi(eq(n(), v(1), v(0)), eq(n(), v(2), v(1)))));
    assert!(k.check(&term, &ty).is_err());
    let proof_ty = eq(n(), z(), z());
    let a = lam(proof_ty.clone(), lam(proof_ty.clone(), v(1)));
    let b = lam(proof_ty.clone(), lam(proof_ty.clone(), v(0)));
    assert!(!k
        .equivalent(
            &a,
            &b,
            &pi(proof_ty.clone(), pi(proof_ty.clone(), proof_ty))
        )
        .unwrap());
}
#[test]
fn j_can_return_a_type_in_a_higher_universe() {
    let term = T::J {
        level: 1,
        ty: n(),
        left: z(),
        motive: lam(n(), lam(eq(n(), z(), v(0)), T::Universe(0).arc())),
        base: n(),
        right: z(),
        proof: refl(n(), z()),
    }
    .arc();
    assert_eq!(Kernel::default().normalize(&term).unwrap(), n());
}
#[test]
fn equality_respects_budget_and_level_overflow() {
    assert_eq!(
        Kernel::new(1).infer(&refl(n(), z())),
        Err(Error::BudgetExceeded)
    );
    let term = T::J {
        level: u32::MAX,
        ty: n(),
        left: z(),
        motive: constant_motive(),
        base: z(),
        right: z(),
        proof: refl(n(), z()),
    }
    .arc();
    assert_eq!(Kernel::default().infer(&term), Err(Error::UniverseOverflow));
}
