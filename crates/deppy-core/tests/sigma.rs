use deppy_core::{Error, Kernel, Relevance, Term as T, Tm};
fn nat() -> Tm {
    T::Nat.arc()
}
fn zero() -> Tm {
    T::Zero.arc()
}
fn var(n: usize) -> Tm {
    T::Var(n).arc()
}
fn sigma(a: Tm, b: Tm) -> Tm {
    T::Sigma {
        domain: a,
        codomain: b,
    }
    .arc()
}
fn pair(ty: Tm, fst: Tm, snd: Tm) -> Tm {
    T::Pair { ty, fst, snd }.arc()
}
fn fst(p: Tm) -> Tm {
    T::Fst(p).arc()
}
fn snd(p: Tm) -> Tm {
    T::Snd(p).arc()
}
fn lam(domain: Tm, body: Tm) -> Tm {
    T::Lam {
        relevance: Relevance::Runtime,
        domain,
        body,
    }
    .arc()
}
fn vec(n: Tm) -> Tm {
    T::Vec { ty: nat(), len: n }.arc()
}
fn packed_ty() -> Tm {
    sigma(nat(), vec(var(0)))
}
fn packed() -> Tm {
    pair(packed_ty(), zero(), T::VNil { ty: nat() }.arc())
}
#[test]
fn dependent_pair_and_projections_compute() {
    let k = Kernel::default();
    let p = packed();
    assert_eq!(k.infer(&p).unwrap(), packed_ty());
    assert_eq!(k.normalize(&fst(p.clone())).unwrap(), zero());
    assert_eq!(k.infer(&snd(p.clone())).unwrap(), vec(zero()));
    assert_eq!(k.normalize(&snd(p)).unwrap(), T::VNil { ty: nat() }.arc());
}
#[test]
fn neutral_second_projection_keeps_first_projection_in_type() {
    let k = Kernel::default();
    let f = lam(packed_ty(), snd(var(0)));
    let expected = T::Pi {
        relevance: Relevance::Runtime,
        domain: packed_ty(),
        codomain: vec(fst(var(0))),
    }
    .arc();
    k.check(&f, &expected).unwrap();
    assert_eq!(k.normalize(&f).unwrap(), f);
}
#[test]
fn nested_binders_and_type_valued_components() {
    let k = Kernel::default();
    let ty = sigma(T::Universe(0).arc(), var(0));
    let p = pair(ty.clone(), nat(), zero());
    assert_eq!(k.infer(&ty).unwrap(), T::Universe(1).arc());
    assert_eq!(k.infer(&snd(p)).unwrap(), nat());
    let f = lam(
        T::Universe(0).arc(),
        lam(sigma(var(0), var(1)), snd(var(0))),
    );
    assert_eq!(k.normalize(&f).unwrap(), f);
}
#[test]
fn universes_are_maximal_and_non_cumulative() {
    let k = Kernel::default();
    for (a, b) in [(0, 2), (2, 0), (1, 1)] {
        assert_eq!(
            k.infer(&sigma(T::Universe(a).arc(), T::Universe(b).arc()))
                .unwrap(),
            T::Universe(a.max(b) + 1).arc()
        );
    }
    assert!(k.check(&packed_ty(), &T::Universe(1).arc()).is_err());
    assert!(k.infer(&sigma(T::Universe(u32::MAX).arc(), nat())).is_err());
}
#[test]
fn rejects_bad_families_annotations_and_components_before_projection() {
    let k = Kernel::default();
    for p in [
        pair(nat(), zero(), zero()),
        pair(packed_ty(), nat(), zero()),
        pair(
            packed_ty(),
            T::Succ(zero()).arc(),
            T::VNil { ty: nat() }.arc(),
        ),
        pair(sigma(nat(), zero()), zero(), zero()),
        pair(sigma(nat(), nat()), zero(), nat()),
    ] {
        assert!(k.infer(&p).is_err());
        assert!(k.normalize(&fst(p)).is_err());
    }
    assert!(k.infer(&snd(zero())).is_err());
    assert!(k.infer(&sigma(nat(), var(1))).is_err());
}
#[test]
fn sigma_has_no_eta_rule() {
    let k = Kernel::default();
    let ty = packed_ty();
    let identity = lam(ty.clone(), var(0));
    let expanded = lam(ty.clone(), pair(ty.clone(), fst(var(0)), snd(var(0))));
    let fty = T::Pi {
        relevance: Relevance::Runtime,
        domain: ty.clone(),
        codomain: ty,
    }
    .arc();
    assert!(!k.equivalent(&identity, &expanded, &fty).unwrap());
}
#[test]
fn pair_comparison_checks_both_components_and_budget() {
    let k = Kernel::default();
    let ty = sigma(nat(), nat());
    let a = pair(ty.clone(), zero(), zero());
    for b in [
        pair(ty.clone(), T::Succ(zero()).arc(), zero()),
        pair(ty.clone(), zero(), T::Succ(zero()).arc()),
    ] {
        assert!(!k.equivalent(&a, &b, &ty).unwrap());
    }
    assert_eq!(
        Kernel::new(1).normalize(&packed()),
        Err(Error::BudgetExceeded)
    );
}
