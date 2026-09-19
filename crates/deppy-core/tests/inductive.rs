use deppy_core::{Error, InductiveDecl, Kernel, Relevance, Term as T, Tm};
fn n() -> Tm {
    T::Nat.arc()
}
fn z() -> Tm {
    T::Zero.arc()
}
fn v(i: usize) -> Tm {
    T::Var(i).arc()
}
fn lam(d: Tm, b: Tm) -> Tm {
    T::Lam {
        relevance: Relevance::Runtime,
        domain: d,
        body: b,
    }
    .arc()
}
fn app(f: Tm, a: Tm) -> Tm {
    T::App {
        function: f,
        argument: a,
    }
    .arc()
}
fn ty(id: u64) -> Tm {
    T::Inductive {
        id,
        parameters: vec![n()],
    }
    .arc()
}
fn decl() -> InductiveDecl {
    InductiveDecl {
        parameters: vec![T::Universe(0).arc()],
        fields: vec![n(), T::Vec(v(1), v(0)).arc()],
        level: 0,
    }
}
fn ctor(id: u64) -> Tm {
    T::Constructor {
        id,
        parameters: vec![n()],
        fields: vec![z(), T::VNil(n()).arc()],
    }
    .arc()
}
fn kernel() -> Kernel {
    let mut k = Kernel::default();
    k.declare(1, decl()).unwrap();
    k
}
#[test]
fn dependent_constructor_and_generated_projections() {
    let k = kernel();
    assert_eq!(k.infer(&ctor(1)).unwrap(), ty(1));
    let ps = k.projection_functions(1).unwrap();
    assert_eq!(
        k.normalize(&app(app(ps[0].clone(), n()), ctor(1))).unwrap(),
        z()
    );
    assert_eq!(
        k.normalize(&app(app(ps[1].clone(), n()), ctor(1))).unwrap(),
        T::VNil(n()).arc()
    );
    let getter = lam(ty(1), app(app(ps[1].clone(), n()), v(0)));
    let expected = T::Pi {
        relevance: Relevance::Runtime,
        domain: ty(1),
        codomain: T::Vec(n(), app(app(ps[0].clone(), n()), v(0))).arc(),
    }
    .arc();
    k.check(&getter, &expected).unwrap();
    let nf = k.normalize(&getter).unwrap();
    k.check(&nf, &expected).unwrap();
}
#[test]
fn same_shape_declarations_are_nominal_and_not_sigma() {
    let mut k = kernel();
    k.declare(2, decl()).unwrap();
    assert!(k.check(&ctor(1), &ty(2)).is_err());
    assert!(!k.equivalent(&ty(1), &ty(2), &T::Universe(0).arc()).unwrap());
    assert!(k
        .check(
            &ctor(1),
            &T::Sigma {
                domain: n(),
                codomain: T::Vec(n(), v(0)).arc()
            }
            .arc()
        )
        .is_err());
    assert_eq!(k.declare(1, decl()), Err(Error::DuplicateInductive(1)));
}
#[test]
fn declarations_reject_recursion_forward_references_scope_and_bad_universes() {
    let mut k = kernel();
    for fields in [
        vec![ty(3)],
        vec![ty(4)],
        vec![v(1)],
        vec![z()],
        vec![T::Universe(0).arc()],
    ] {
        assert!(k
            .declare(
                3,
                InductiveDecl {
                    parameters: vec![],
                    fields,
                    level: 0
                }
            )
            .is_err());
        assert!(k.declaration(3).is_err());
    }
    assert!(k
        .declare(
            3,
            InductiveDecl {
                parameters: vec![z()],
                fields: vec![],
                level: 0
            }
        )
        .is_err());
    assert!(k
        .declare(
            3,
            InductiveDecl {
                parameters: vec![],
                fields: vec![],
                level: u32::MAX
            }
        )
        .is_err());
}
#[test]
fn invalid_constructor_arguments_and_unknown_ids_are_rejected() {
    let k = kernel();
    assert!(k.infer(&ctor(5)).is_err());
    for parameters in [vec![], vec![z()], vec![n(), n()]] {
        assert!(k.infer(&T::Inductive { id: 1, parameters }.arc()).is_err());
    }
    for fields in [
        vec![],
        vec![z(), z()],
        vec![T::Succ(z()).arc(), T::VNil(n()).arc()],
    ] {
        assert!(k
            .infer(
                &T::Constructor {
                    id: 1,
                    parameters: vec![n()],
                    fields
                }
                .arc()
            )
            .is_err());
    }
    assert!(Kernel::default().infer(&ctor(1)).is_err());
}
#[test]
fn dependent_motive_observes_constructor_and_iota() {
    let k = kernel();
    let r = ty(1);
    let motive = lam(
        r.clone(),
        T::Eq {
            ty: r.clone(),
            left: v(0),
            right: v(0),
        }
        .arc(),
    );
    let c = T::Constructor {
        id: 1,
        parameters: vec![n()],
        fields: vec![v(1), v(0)],
    }
    .arc();
    let branch = lam(
        n(),
        lam(
            T::Vec(n(), v(0)).arc(),
            T::Refl {
                ty: r.clone(),
                value: c,
            }
            .arc(),
        ),
    );
    let elim = T::Elim {
        id: 1,
        parameters: vec![n()],
        level: 0,
        motive,
        branch,
        scrutinee: ctor(1),
    }
    .arc();
    assert_eq!(
        k.normalize(&elim).unwrap(),
        T::Refl {
            ty: r,
            value: ctor(1)
        }
        .arc()
    );
}
#[test]
fn all_eliminator_fields_are_checked_before_iota() {
    let k = kernel();
    let motive = lam(ty(1), n());
    let branch = lam(n(), lam(T::Vec(n(), v(0)).arc(), z()));
    for (id, parameters, level, motive, branch, scrutinee) in [
        (2, vec![n()], 0, motive.clone(), branch.clone(), ctor(1)),
        (1, vec![z()], 0, motive.clone(), branch.clone(), ctor(1)),
        (1, vec![n()], 1, motive.clone(), branch.clone(), ctor(1)),
        (1, vec![n()], 0, lam(n(), n()), branch.clone(), ctor(1)),
        (
            1,
            vec![n()],
            0,
            motive.clone(),
            lam(n(), lam(n(), z())),
            ctor(1),
        ),
        (1, vec![n()], 0, motive.clone(), branch.clone(), z()),
        (1, vec![n()], u32::MAX, motive, branch, ctor(1)),
    ] {
        assert!(k
            .normalize(
                &T::Elim {
                    id,
                    parameters,
                    level,
                    motive,
                    branch,
                    scrutinee
                }
                .arc()
            )
            .is_err());
    }
}
#[test]
fn empty_and_type_valued_records_and_earlier_declarations() {
    let mut k = kernel();
    k.declare(
        2,
        InductiveDecl {
            parameters: vec![],
            fields: vec![],
            level: 0,
        },
    )
    .unwrap();
    let unit = T::Constructor {
        id: 2,
        parameters: vec![],
        fields: vec![],
    }
    .arc();
    let elim = T::Elim {
        id: 2,
        parameters: vec![],
        level: 0,
        motive: lam(
            T::Inductive {
                id: 2,
                parameters: vec![],
            }
            .arc(),
            n(),
        ),
        branch: z(),
        scrutinee: unit,
    }
    .arc();
    assert_eq!(k.normalize(&elim).unwrap(), z());
    assert!(k.projection_functions(2).unwrap().is_empty());
    k.declare(
        3,
        InductiveDecl {
            parameters: vec![],
            fields: vec![T::Universe(0).arc(), v(0), ty(1)],
            level: 1,
        },
    )
    .unwrap();
    let p = T::Constructor {
        id: 3,
        parameters: vec![],
        fields: vec![n(), z(), ctor(1)],
    }
    .arc();
    for (projection, expected) in
        k.projection_functions(3)
            .unwrap()
            .into_iter()
            .zip([n(), z(), ctor(1)])
    {
        assert_eq!(k.normalize(&app(projection, p.clone())).unwrap(), expected);
    }
}
#[test]
fn budget_and_no_record_eta() {
    assert!(Kernel::new(1).declare(1, decl()).is_err());
    let k = kernel();
    let ps = k.projection_functions(1).unwrap();
    let expanded = lam(
        ty(1),
        T::Constructor {
            id: 1,
            parameters: vec![n()],
            fields: ps.into_iter().map(|p| app(app(p, n()), v(0))).collect(),
        }
        .arc(),
    );
    let identity = lam(ty(1), v(0));
    let fty = k.infer(&identity).unwrap();
    assert!(!k.equivalent(&identity, &expanded, &fty).unwrap());
}
