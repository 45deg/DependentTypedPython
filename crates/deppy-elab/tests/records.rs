use deppy_core::{Relevance, Term};
use deppy_elab::{
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
    Record, RecordDecl,
};
fn n(s: &str) -> E {
    E::name(s)
}
fn decl() -> RecordDecl {
    RecordDecl {
        parameters: vec![("A".into(), E::Universe(0))],
        fields: vec![
            ("n".into(), E::Nat),
            ("value".into(), E::vec(n("A"), n("n"))),
        ],
        level: 0,
    }
}
fn setup() -> (Elaborator, Record) {
    let mut e = Elaborator::default();
    let r = e.declare_record(1, decl()).unwrap();
    (e, r)
}
fn sigma(a: E) -> E {
    E::sigma("k", E::Nat, E::vec(a, n("k")))
}
fn lam(s: &str, t: E, b: E) -> E {
    E::lam(s, Explicit, Some(t), b)
}
fn ctor(r: &Record) -> E {
    r.constructor().app(E::Zero).app(E::vnil(E::Nat))
}
fn conversions(r: &Record) -> (E, E) {
    let to_record = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        lam(
            "p",
            sigma(n("A")),
            r.constructor().app(n("p").fst()).app(n("p").snd()),
        ),
    );
    let to_pair = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        lam(
            "r",
            r.ty().implicit(n("A")),
            E::pair(
                r.projection("n").unwrap().app(n("r")),
                r.projection("value").unwrap().app(n("r")),
            )
            .ann(sigma(n("A"))),
        ),
    );
    (to_record, to_pair)
}
#[test]
fn some_vec_constructor_infers_implicit_carrier_and_projections() {
    let (e, r) = setup();
    let value = e.infer(&ctor(&r)).unwrap();
    e.kernel()
        .check(
            &value.term,
            &e.infer(&r.ty().implicit(E::Nat)).unwrap().term,
        )
        .unwrap();
    for (name, expected) in [("n", E::Zero), ("value", E::vnil(E::Nat))] {
        let out = e.infer(&r.projection(name).unwrap().app(ctor(&r))).unwrap();
        assert_eq!(
            e.kernel().normalize(&out.term).unwrap(),
            e.infer(&expected).unwrap().term
        );
    }
    assert!(r.projection("missing").is_err());
}
#[test]
fn sigma_and_record_conversions_check_generally_and_compute() {
    let (e, r) = setup();
    let (a, b) = conversions(&r);
    e.infer(&a).unwrap();
    e.infer(&b).unwrap();
    let pair = E::pair(E::Zero, E::vnil(E::Nat)).ann(sigma(E::Nat));
    let result = e.infer(&b.app(a.app(pair.clone()))).unwrap();
    assert_eq!(
        e.kernel().normalize(&result.term).unwrap(),
        e.kernel().normalize(&e.infer(&pair).unwrap().term).unwrap()
    );
}
#[test]
fn nominal_identity_and_sigma_are_not_interchangeable() {
    let (mut e, r) = setup();
    let other = e.declare_record(2, decl()).unwrap();
    assert!(e.check(&ctor(&r), &other.ty().implicit(E::Nat)).is_err());
    assert!(e.check(&ctor(&r), &sigma(E::Nat)).is_err());
    assert!(e
        .infer(&other.projection("value").unwrap().app(ctor(&r)))
        .is_err());
    assert!(e.declare_record(1, decl()).is_err());
}
#[test]
fn invalid_declarations_are_atomic_and_ordered() {
    let (mut e, _) = setup();
    for fields in [
        vec![("x".into(), n("x"))],
        vec![("x".into(), n("y")), ("y".into(), E::Universe(0))],
        vec![("x".into(), E::Nat), ("x".into(), E::Nat)],
        vec![("".into(), E::Nat)],
        vec![("x".into(), E::Zero)],
        vec![("x".into(), E::Universe(0))],
    ] {
        assert!(e
            .declare_record(
                3,
                RecordDecl {
                    parameters: vec![],
                    fields,
                    level: 0
                }
            )
            .is_err());
        assert!(e.kernel().declaration(3).is_err());
    }
    e.declare_record(
        3,
        RecordDecl {
            parameters: vec![],
            fields: vec![],
            level: 0,
        },
    )
    .unwrap();
}
#[test]
fn wrong_fields_and_incomplete_constructor_are_rejected() {
    let (e, r) = setup();
    assert!(e
        .infer(&r.constructor().app(E::Zero.succ()).app(E::vnil(E::Nat)))
        .is_err());
    assert!(e
        .infer(&r.constructor().app(E::Nat).app(E::vnil(E::Nat)))
        .is_err());
    assert!(e
        .infer(
            &r.constructor()
                .app(E::Zero)
                .app(E::vnil(E::Nat))
                .app(E::Zero)
        )
        .is_err());
    assert!(e
        .check(
            &r.constructor().implicit(E::Nat).app(E::Zero),
            &r.ty().implicit(E::Nat)
        )
        .is_err());
}
#[test]
fn dependent_parameters_and_three_fields_preserve_scopes() {
    let mut e = Elaborator::default();
    let r = e
        .declare_record(
            1,
            RecordDecl {
                parameters: vec![("A".into(), E::Universe(0)), ("a".into(), n("A"))],
                fields: vec![
                    ("b".into(), n("A")),
                    ("p".into(), E::eq(n("A"), n("a"), n("b"))),
                    (
                        "q".into(),
                        E::eq(E::eq(n("A"), n("a"), n("b")), n("p"), n("p")),
                    ),
                ],
                level: 0,
            },
        )
        .unwrap();
    let value = r
        .constructor()
        .implicit(E::Nat)
        .implicit(E::Zero)
        .app(E::Zero)
        .app(E::Zero.refl())
        .app(E::Zero.refl().refl());
    let q = e.infer(&r.projection("q").unwrap().app(value)).unwrap();
    assert_eq!(
        e.kernel().normalize(&q.term).unwrap(),
        e.infer(&E::Zero.refl().refl()).unwrap().term
    );
}
#[test]
fn higher_universe_and_empty_record() {
    let mut e = Elaborator::default();
    let r = e
        .declare_record(
            1,
            RecordDecl {
                parameters: vec![],
                fields: vec![("A".into(), E::Universe(0)), ("x".into(), n("A"))],
                level: 1,
            },
        )
        .unwrap();
    let p = r.constructor().app(E::Nat).app(E::Zero);
    assert_eq!(
        e.kernel()
            .normalize(&e.infer(&r.projection("x").unwrap().app(p)).unwrap().term)
            .unwrap(),
        Term::Zero.arc()
    );
    let r = e
        .declare_record(
            2,
            RecordDecl {
                parameters: vec![],
                fields: vec![],
                level: 0,
            },
        )
        .unwrap();
    e.check(&r.constructor(), &r.ty()).unwrap();
}
#[test]
fn embedded_core_is_checked_and_let_import_keeps_dependencies() {
    let (e, r) = setup();
    assert!(Elaborator::default().infer(&r.constructor()).is_err());
    assert!(e.infer(&E::Core(Term::Var(0).arc())).is_err());
    let bad = Term::Fst(
        Term::Pair {
            ty: Term::Sigma {
                domain: Term::Nat.arc(),
                codomain: Term::Nat.arc(),
            }
            .arc(),
            fst: Term::Zero.arc(),
            snd: Term::Nat.arc(),
        }
        .arc(),
    )
    .arc();
    assert!(e.infer(&E::Core(bad)).is_err());
    let let_ty = Term::Let {
        ty: Term::Universe(0).arc(),
        value: Term::Nat.arc(),
        body: Term::Lam {
            relevance: Relevance::Runtime,
            domain: Term::Var(0).arc(),
            body: Term::Var(0).arc(),
        }
        .arc(),
    }
    .arc();
    let result = e.infer(&E::Core(let_ty).app(E::Zero)).unwrap();
    assert_eq!(
        e.kernel().normalize(&result.term).unwrap(),
        Term::Zero.arc()
    );
}
#[test]
fn missing_parameters_and_budget_are_not_guessed() {
    let (e, r) = setup();
    assert!(matches!(
        e.infer(&r.constructor().app(E::Zero)),
        Err(Error::UnsolvedMeta { .. })
    ));
    assert!(Elaborator::new(1).declare_record(1, decl()).is_err());
}
