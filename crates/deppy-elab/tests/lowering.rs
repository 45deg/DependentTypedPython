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

fn index(bound: usize, position: usize) -> E {
    if position == 0 {
        E::fz(num(bound - 1))
    } else {
        E::fs(num(bound - 1), index(bound - 1, position - 1))
    }
}
#[test]
fn nested_fin_split_lowers_get_and_computes_every_position() {
    let e = Elaborator::default();
    let f = structural::get(0);
    let checked = e.compile_function(&f).unwrap();
    e.kernel()
        .check(&checked.term, &e.infer(&prelude::vec_get(0)).unwrap().ty)
        .unwrap();
    let get = e.lower_function(&f).unwrap();
    for len in 1..5 {
        let items = (1..=len).collect::<Vec<_>>();
        for i in 0..len {
            let out = e
                .infer(
                    &get.clone()
                        .app(num(len))
                        .app(vector(&items))
                        .app(index(len, i)),
                )
                .unwrap();
            assert_eq!(
                e.kernel().normalize(&out.term).unwrap(),
                e.infer(&num(items[i])).unwrap().term
            );
        }
    }
    e.compile_function(&structural::get(1)).unwrap();
    let get_types = e.lower_function(&structural::get(1)).unwrap();
    let out = e
        .infer(
            &get_types
                .app(num(1))
                .app(E::vcons(
                    E::Universe(0),
                    E::Zero,
                    E::Nat,
                    E::vnil(E::Universe(0)),
                ))
                .app(E::fz(E::Zero)),
        )
        .unwrap();
    assert_eq!(e.kernel().normalize(&out.term).unwrap(), Term::Nat.arc());
}
#[test]
fn get_preserves_symbolic_tail_computation() {
    let e = Elaborator::default();
    let get = e.lower_function(&structural::get(0)).unwrap();
    let mut left = get
        .clone()
        .app(n("k").succ())
        .app(E::vcons(E::Nat, n("k"), n("h"), n("t")))
        .app(E::fs(n("k"), n("j")));
    let mut right = get.app(n("k")).app(n("t")).app(n("j"));
    for (name, ty) in [
        ("j", E::fin(n("k"))),
        ("t", E::vec(E::Nat, n("k"))),
        ("h", E::Nat),
        ("k", E::Nat),
    ] {
        left = E::lam(name, Explicit, Some(ty.clone()), left);
        right = E::lam(name, Explicit, Some(ty), right);
    }
    let a = e.infer(&left).unwrap();
    let b = e.infer(&right).unwrap();
    assert!(e.kernel().equivalent(&a.term, &b.term, &a.ty).unwrap());
}
#[test]
fn nested_branches_reject_missing_coverage_wrong_arguments_and_shadowing() {
    let e = Elaborator::default();
    for mode in 0..5 {
        let mut f = structural::get(0);
        let Body::Match { arms, .. } = &mut step(&mut f).body else {
            panic!()
        };
        match mode {
            0 => {
                arms.pop();
            }
            1 => arms[1].body = Body::Return(E::Recur(vec![n("A"), n("k"), n("t"), n("i")])),
            2 => arms[1].body = Body::Return(E::Recur(vec![n("A"), n("k"), n("xs"), n("j")])),
            3 => {
                arms[1].pattern = Pattern::FS {
                    bound: "k".into(),
                    pred: "j".into(),
                }
            }
            _ => arms[0].body = Body::Return(E::Zero),
        }
        assert!(e.compile_function(&f).is_err());
    }
}
#[test]
fn unsupported_nested_motives_are_rejected_without_index_coercion() {
    let e = Elaborator::default();
    let mut f = structural::get(0);
    f.result = E::eq(E::fin(n("n")), n("i"), n("i"));
    assert!(e.compile_function(&f).is_err());
    f = structural::get(0);
    let Body::Match { scrutinee, .. } = &mut step(&mut f).body else {
        panic!()
    };
    *scrutinee = "t".into();
    assert!(matches!(
        e.compile_function(&f),
        Err(Error::UnsupportedMatch(_))
    ));
    f = structural::get(0);
    f.parameters.push(Parameter {
        name: "extra".into(),
        plicity: Explicit,
        ty: E::Nat,
    });
    assert!(e.compile_function(&f).is_err());
    // Fin Z is handled by fin0_elim, never by silently dropping branches.
    f = structural::get(0);
    let nested = step(&mut f).body.clone();
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms[0].body = nested;
    assert!(e.compile_function(&f).is_err());
}
#[test]
fn motives_can_depend_on_the_entire_matched_value() {
    let e = Elaborator::default();
    let f = Function {
        parameters: vec![
            Parameter {
                name: "n".into(),
                plicity: Explicit,
                ty: E::Nat,
            },
            Parameter {
                name: "xs".into(),
                plicity: Explicit,
                ty: E::vec(E::Nat, n("n")),
            },
        ],
        result: E::eq(E::vec(E::Nat, n("n")), n("xs"), n("xs")),
        decreases: "xs".into(),
        motive_level: 0,
        body: Body::Match {
            scrutinee: "xs".into(),
            arms: vec![
                Arm {
                    pattern: Pattern::VNil,
                    body: Body::Return(n("xs").refl()),
                },
                Arm {
                    pattern: Pattern::VCons {
                        len: "k".into(),
                        head: "h".into(),
                        tail: "t".into(),
                    },
                    body: Body::Return(n("xs").refl()),
                },
            ],
        },
    };
    e.compile_function(&f).unwrap();
    let f = Function {
        parameters: vec![
            Parameter {
                name: "n".into(),
                plicity: Explicit,
                ty: E::Nat,
            },
            Parameter {
                name: "i".into(),
                plicity: Explicit,
                ty: E::fin(n("n")),
            },
        ],
        result: E::eq(E::fin(n("n")), n("i"), n("i")),
        decreases: "i".into(),
        motive_level: 0,
        body: Body::Match {
            scrutinee: "i".into(),
            arms: vec![
                Arm {
                    pattern: Pattern::FZ("k".into()),
                    body: Body::Return(n("i").refl()),
                },
                Arm {
                    pattern: Pattern::FS {
                        bound: "k".into(),
                        pred: "j".into(),
                    },
                    body: Body::Return(n("i").refl()),
                },
            ],
        },
    };
    e.compile_function(&f).unwrap();
}

#[test]
fn later_arguments_can_change_and_branch_order_is_irrelevant() {
    let e = Elaborator::default();
    let mut f = structural::add();
    step(&mut f).body = Body::Return(E::Recur(vec![n("k"), n("m").succ()]));
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms.reverse();
    let out = e
        .infer(&e.lower_function(&f).unwrap().app(num(2)).app(num(3)))
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&out.term).unwrap(),
        e.infer(&num(5)).unwrap().term
    );
}
#[test]
fn return_only_functions_and_parameter_shadowing() {
    let e = Elaborator::default();
    let mut f = structural::add();
    f.body = Body::Return(n("n"));
    e.compile_function(&f).unwrap();
    f = structural::add();
    step(&mut f).pattern = Pattern::Succ("m".into());
    assert!(matches!(
        e.compile_function(&f),
        Err(Error::InvalidPattern(_))
    ));
    f = structural::get(0);
    step(&mut f).pattern = Pattern::VCons {
        len: "k".into(),
        head: "i".into(),
        tail: "t".into(),
    };
    assert!(e.compile_function(&f).is_err());
}

#[test]
fn body_lets_support_nested_terminal_bodies_and_preserve_computation() {
    let mut f = structural::get(0);
    let Body::Match { arms, .. } = &mut step(&mut f).body else {
        panic!()
    };
    for arm in arms {
        let Body::Return(value) = &arm.body else {
            panic!()
        };
        arm.body = Body::Let {
            name: "answer".into(),
            ty: Some(n("A")),
            value: value.clone(),
            body: Box::new(Body::Return(n("answer"))),
        };
    }
    f.body = Body::Let {
        name: "saved".into(),
        ty: Some(E::vec(n("A"), n("n"))),
        value: n("xs"),
        body: Box::new(f.body),
    };
    let e = Elaborator::default();
    let lowered = e.lower_function(&f).unwrap();
    let got = e
        .infer(
            &lowered
                .app(num(2))
                .app(vector(&[3, 4]))
                .app(E::fs(num(1), E::fz(num(0)))),
        )
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&got.term).unwrap(),
        e.infer(&num(4)).unwrap().term
    );
}

#[test]
fn body_lets_reject_invalid_generic_values_shadowing_and_forward_names() {
    for (name, ty, value) in [
        ("unused", Some(E::Nat), E::Universe(0)),
        (
            "unused",
            Some(E::eq(E::Nat, n("n"), E::Zero)),
            E::refl(n("n")),
        ),
        ("n", None, E::Zero),
        ("unused", None, n("later")),
        ("unused", None, E::Recur(vec![n("n"), n("m")])),
    ] {
        let mut f = structural::add();
        f.body = Body::Let {
            name: name.into(),
            ty,
            value,
            body: Box::new(f.body),
        };
        assert!(Elaborator::default().compile_function(&f).is_err());
    }
}
