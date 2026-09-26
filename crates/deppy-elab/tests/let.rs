use deppy_core::Term;
use deppy_elab::{Elaborator, Error, Expr as E, Plicity::Explicit};
fn n(name: &str) -> E {
    E::name(name)
}
#[test]
fn definitions_reduce_in_dependent_types() {
    let e = Elaborator::default();
    let value = E::let_in(
        "A",
        Some(E::Universe(0)),
        E::Nat,
        E::let_in(
            "z",
            Some(n("A")),
            E::Zero,
            E::vnil(n("A")).ann(E::vec(n("A"), n("z"))),
        ),
    );
    let out = e.infer(&value).unwrap();
    assert_eq!(
        e.kernel().normalize(&out.ty).unwrap(),
        e.infer(&E::vec(E::Nat, E::Zero)).unwrap().term
    );
}
#[test]
fn shadowing_and_outer_capture() {
    let e = Elaborator::default();
    let body = E::let_in(
        "x",
        None,
        n("x").succ(),
        E::let_in("x", None, n("x").succ(), n("x")),
    );
    let f = E::lam("x", Explicit, Some(E::Nat), body).app(E::Zero);
    assert_eq!(
        e.kernel().normalize(&e.infer(&f).unwrap().term).unwrap(),
        Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
    );
    assert!(matches!(
        e.infer(&E::let_in("x", None, n("x"), E::Zero)),
        Err(Error::UnknownName(_))
    ));
}
#[test]
fn expected_type_reaches_let_body_and_annotated_value() {
    let e = Elaborator::default();
    let sigma = E::sigma("k", E::Nat, E::vec(E::Nat, n("k")));
    e.check(
        &E::let_in("v", None, E::vnil(E::Nat), E::pair(E::Hole, n("v"))),
        &sigma,
    )
    .unwrap();
    e.infer(&E::let_in(
        "p",
        Some(sigma),
        E::pair(E::Zero, E::vnil(E::Nat)),
        n("p"),
    ))
    .unwrap();
}
#[test]
fn metas_under_aliases_remain_scoped_and_checked() {
    let e = Elaborator::default();
    let body = E::let_in("z", None, n("x"), E::pair(E::Hole, E::refl(n("z")))).ann(E::sigma(
        "k",
        E::Nat,
        E::eq(E::Nat, n("k"), n("x")),
    ));
    e.infer(&E::lam("x", Explicit, Some(E::Nat), body)).unwrap();
    assert!(matches!(
        e.infer(&E::let_in("unused", Some(E::Nat), E::Hole, E::Zero)),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn unused_invalid_values_are_rejected() {
    let e = Elaborator::default();
    assert!(e
        .infer(&E::let_in("unused", Some(E::Nat), E::Universe(0), E::Zero))
        .is_err());
    assert!(e
        .infer(&E::let_in(
            "unused",
            None,
            E::Core(Term::Var(0).arc()),
            E::Zero
        ))
        .is_err());
    assert!(e
        .infer(&E::let_in("unused", Some(E::Zero), E::Zero, E::Zero))
        .is_err());
}
#[test]
fn lowering_preserves_let_scope_and_recursion_checks() {
    use deppy_elab::{lower::Body, prelude::structural};
    let e = Elaborator::default();
    let mut f = structural::add();
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms[1].body = Body::Return(E::let_in(
        "answer",
        None,
        E::Recur(vec![n("k"), n("m")]),
        n("answer").succ(),
    ));
    e.compile_function(&f).unwrap();
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms[1].body = Body::Return(E::let_in("k", None, n("k"), E::Recur(vec![n("k"), n("m")])));
    assert!(matches!(
        e.compile_function(&f),
        Err(Error::InvalidRecursion(_))
    ));
}

#[test]
fn shared_definition_is_preserved_as_a_core_let() {
    let e = Elaborator::default();
    let pair = E::pair(n("v"), n("v")).ann(E::sigma("a", E::Nat, E::Nat));
    let out = e
        .infer(&E::let_in("v", Some(E::Nat), E::Zero.succ(), pair))
        .unwrap();
    let Term::Let { body, .. } = out.term.as_ref() else {
        panic!("definition was expanded instead of shared")
    };
    let Term::Pair { fst, snd, .. } = body.as_ref() else {
        panic!("expected pair")
    };
    assert_eq!(fst.as_ref(), &Term::Var(0));
    assert_eq!(snd.as_ref(), &Term::Var(0));
    e.kernel().check(&out.term, &out.ty).unwrap();
}

#[test]
fn shared_function_reused_under_distinct_binders_does_not_capture() {
    let e = Elaborator::default();
    let f = E::lam(
        "x",
        Explicit,
        Some(E::Nat),
        E::lam("y", Explicit, Some(E::Nat), n("x")),
    );
    let value = E::let_in(
        "f",
        None,
        f,
        E::let_in(
            "g",
            None,
            n("f").app(E::Zero),
            n("f").app(E::Zero.succ()).app(n("g").app(E::Zero.succ())),
        ),
    );
    assert_eq!(
        e.kernel()
            .normalize(&e.infer(&value).unwrap().term)
            .unwrap(),
        Term::Succ(Term::Zero.arc()).arc()
    );
}
