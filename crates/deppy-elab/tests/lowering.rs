use deppy_core::Term;
use deppy_elab::{
    lower::{Arm, Body, Function, Parameter, Pattern},
    prelude::{self, structural},
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(s: &str) -> E {
    E::name(s)
}
fn num(x: usize) -> E {
    (0..x).fold(E::Zero, |n, _| n.succ())
}
fn vector(xs: &[usize]) -> E {
    xs.iter()
        .rev()
        .enumerate()
        .fold(E::vnil(E::Nat), |tail, (k, x)| {
            E::vcons(E::Nat, num(k), num(*x), tail)
        })
}
fn step(f: &mut Function) -> &mut Arm {
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    &mut arms[1]
}
#[test]
fn lower_nat_recursion_and_induction() {
    let e = Elaborator::default();
    for f in [structural::add(), structural::zero_right()] {
        e.compile_function(&f).unwrap();
    }
    let add = e.lower_function(&structural::add()).unwrap();
    for a in 0..4 {
        for b in 0..4 {
            let out = e.infer(&add.clone().app(num(a)).app(num(b))).unwrap();
            assert_eq!(
                e.kernel().normalize(&out.term).unwrap(),
                e.infer(&num(a + b)).unwrap().term
            );
        }
    }
    let proof = e
        .infer(
            &e.lower_function(&structural::zero_right())
                .unwrap()
                .app(num(3)),
        )
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&proof.term).unwrap(),
        e.infer(&num(3).refl()).unwrap().term
    );
}
#[test]
fn lower_append_with_generalized_later_argument() {
    let e = Elaborator::default();
    let f = structural::append(0);
    let checked = e.compile_function(&f).unwrap();
    let oracle = e.infer(&prelude::vec_append(0)).unwrap();
    e.kernel().check(&checked.term, &oracle.ty).unwrap();
    let append = e.lower_function(&f).unwrap();
    for a in 0..4 {
        for b in 0..4 {
            let xs = (0..a).collect::<Vec<_>>();
            let ys = (0..b).collect::<Vec<_>>();
            let expected = vector(&xs.iter().chain(&ys).copied().collect::<Vec<_>>());
            let out = e
                .infer(
                    &append
                        .clone()
                        .app(num(a))
                        .app(num(b))
                        .app(vector(&xs))
                        .app(vector(&ys)),
                )
                .unwrap();
            assert_eq!(
                e.kernel().normalize(&out.term).unwrap(),
                e.infer(&expected).unwrap().term
            );
        }
    }
}
#[test]
fn lower_fin_recursion() {
    let e = Elaborator::default();
    let f = e.lower_function(&structural::fin_rank()).unwrap();
    let i = E::fs(num(2), E::fs(num(1), E::fz(E::Zero)));
    let out = e.infer(&f.app(num(3)).app(i)).unwrap();
    assert_eq!(
        e.kernel().normalize(&out.term).unwrap(),
        e.infer(&num(2)).unwrap().term
    );
}
#[test]
fn rejects_non_decreasing_calls_and_changed_prefix() {
    let e = Elaborator::default();
    for args in [
        vec![n("n"), n("m")],
        vec![n("k").succ(), n("m")],
        vec![n("m"), n("k")],
        vec![n("k")],
    ] {
        let mut f = structural::add();
        step(&mut f).body = Body::Return(E::Recur(args));
        assert!(matches!(
            e.compile_function(&f),
            Err(Error::InvalidRecursion(_))
        ));
    }
    for args in [
        vec![n("A"), n("n"), n("m"), n("t"), n("ys")],
        vec![n("A"), n("k"), E::Zero, n("t"), n("ys")],
        vec![n("A"), n("k"), n("m"), n("xs"), n("ys")],
    ] {
        let mut f = structural::append(0);
        step(&mut f).body = Body::Return(E::Recur(args));
        assert!(matches!(
            e.compile_function(&f),
            Err(Error::InvalidRecursion(_))
        ));
    }
}
#[test]
fn rejects_recursion_in_base_or_without_match() {
    let e = Elaborator::default();
    let mut f = structural::add();
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms[0].body = Body::Return(E::Recur(vec![E::Zero, n("m")]));
    assert!(matches!(
        e.compile_function(&f),
        Err(Error::InvalidRecursion(_))
    ));
    f.body = Body::Return(E::Recur(vec![n("n"), n("m")]));
    assert!(e.compile_function(&f).is_err());
    assert!(e.infer(&E::Recur(vec![])).is_err());
}
#[test]
fn rejects_missing_duplicate_and_wrong_constructor_branches() {
    let e = Elaborator::default();
    for patterns in [
        vec![Pattern::Zero],
        vec![Pattern::Zero, Pattern::Zero],
        vec![Pattern::VNil, Pattern::Succ("k".into())],
    ] {
        let mut f = structural::add();
        f.body = Body::Match {
            scrutinee: "n".into(),
            arms: patterns
                .into_iter()
                .map(|pattern| Arm {
                    pattern,
                    body: Body::Return(E::Zero),
                })
                .collect(),
        };
        assert!(matches!(
            e.compile_function(&f),
            Err(Error::InvalidPattern(_))
        ));
    }
    let mut f = structural::append(0);
    step(&mut f).pattern = Pattern::VCons {
        len: "k".into(),
        head: "x".into(),
        tail: "x".into(),
    };
    assert!(e.compile_function(&f).is_err());
}
#[test]
fn rejects_bad_types_holes_and_universe_claims() {
    let e = Elaborator::default();
    for bad in [E::Nat, E::Hole] {
        let mut f = structural::add();
        step(&mut f).body = Body::Return(bad);
        assert!(e.compile_function(&f).is_err());
    }
    let mut f = structural::add();
    f.motive_level = 1;
    assert!(e.compile_function(&f).is_err());
    f.motive_level = u32::MAX;
    assert!(e.compile_function(&f).is_err());
    f = structural::add();
    f.result = E::Universe(0);
    assert!(e.compile_function(&f).is_err());
}
#[test]
fn hygiene_rejects_shadowed_recursive_child_and_internal_names() {
    let e = Elaborator::default();
    let mut f = structural::add();
    step(&mut f).body = Body::Return(
        E::lam("k", Explicit, Some(E::Nat), E::Recur(vec![n("k"), n("m")])).app(E::Zero),
    );
    assert!(matches!(
        e.compile_function(&f),
        Err(Error::InvalidRecursion(_))
    ));
    step(&mut f).body = Body::Return(n("\0lower0"));
    assert!(e.compile_function(&f).is_err());
    // A lambda with a different binder retains the real structural child.
    step(&mut f).body = Body::Return(
        E::lam("x", Explicit, Some(E::Nat), E::Recur(vec![n("k"), n("m")])).app(E::Zero),
    );
    e.compile_function(&f).unwrap();
}
#[test]
fn higher_universe_and_implicit_generalized_parameter() {
    let e = Elaborator::default();
    e.compile_function(&structural::append(1)).unwrap();
    let f = Function {
        parameters: vec![
            Parameter {
                name: "n".into(),
                plicity: Explicit,
                ty: E::Nat,
            },
            Parameter {
                name: "A".into(),
                plicity: Implicit,
                ty: E::Universe(0),
            },
            Parameter {
                name: "a".into(),
                plicity: Explicit,
                ty: n("A"),
            },
        ],
        result: n("A"),
        decreases: "n".into(),
        motive_level: 1,
        body: Body::Match {
            scrutinee: "n".into(),
            arms: vec![
                Arm {
                    pattern: Pattern::Zero,
                    body: Body::Return(n("a")),
                },
                Arm {
                    pattern: Pattern::Succ("k".into()),
                    body: Body::Return(E::Recur(vec![n("k"), n("A"), n("a")])),
                },
            ],
        },
    };
    let out = e
        .infer(&e.lower_function(&f).unwrap().app(num(2)).app(E::Zero))
        .unwrap();
    assert_eq!(e.kernel().normalize(&out.term).unwrap(), Term::Zero.arc());
}
#[test]
fn decreasing_parameter_and_index_dependencies_are_restricted() {
    let e = Elaborator::default();
    let mut f = structural::append(0);
    f.decreases = "absent".into();
    assert!(e.compile_function(&f).is_err());
    f = structural::append(0);
    f.parameters[2].ty = E::fin(n("n"));
    assert!(e.compile_function(&f).is_err());
    f = structural::append(0);
    f.parameters[3].ty = E::vec(n("A"), n("n").succ());
    assert!(e.compile_function(&f).is_err());
    assert_eq!(
        Elaborator::new(1)
            .lower_function(&structural::add())
            .unwrap_err(),
        Error::BudgetExceeded
    );
}
