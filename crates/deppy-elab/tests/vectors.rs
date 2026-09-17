use deppy_core::Kernel;
use deppy_elab::{
    prelude::{nat_add, vec_append, vec_get},
    Elaborator, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(s: &str) -> E {
    E::name(s)
}
fn nat(i: usize) -> E {
    (0..i).fold(E::Zero, |x, _| x.succ())
}
fn vector(items: &[usize]) -> E {
    items
        .iter()
        .rev()
        .enumerate()
        .fold(E::vnil(E::Nat), |tail, (len, item)| {
            E::vcons(E::Nat, nat(len), nat(*item), tail)
        })
}
fn index(bound: usize, position: usize) -> E {
    assert!(position < bound);
    if position == 0 {
        E::fz(nat(bound - 1))
    } else {
        E::fs(nat(bound - 1), index(bound - 1, position - 1))
    }
}
fn pi(name: &str, ty: E, body: E) -> E {
    E::pi(name, Explicit, ty, body)
}
fn lam(name: &str, ty: E, body: E) -> E {
    E::lam(name, Explicit, Some(ty), body)
}
fn append(a: E, b: E, xs: E, ys: E) -> E {
    vec_append(0).app(a).app(b).app(xs).app(ys)
}
fn get(len: E, xs: E, i: E) -> E {
    vec_get(0).app(len).app(xs).app(i)
}
#[test]
fn append_and_get_check_their_polymorphic_dependent_signatures() {
    let append_ty = E::pi(
        "A",
        Implicit,
        E::Universe(0),
        pi(
            "n",
            E::Nat,
            pi(
                "m",
                E::Nat,
                pi(
                    "xs",
                    E::vec(n("A"), n("n")),
                    pi(
                        "ys",
                        E::vec(n("A"), n("m")),
                        E::vec(n("A"), nat_add().app(n("n")).app(n("m"))),
                    ),
                ),
            ),
        ),
    );
    let get_ty = E::pi(
        "A",
        Implicit,
        E::Universe(0),
        pi(
            "n",
            E::Nat,
            pi(
                "xs",
                E::vec(n("A"), n("n")),
                pi("i", E::fin(n("n")), n("A")),
            ),
        ),
    );
    let elab = Elaborator::default();
    elab.check(&vec_append(0), &append_ty).unwrap();
    elab.check(&vec_get(0), &get_ty).unwrap();
}
#[test]
fn append_preserves_elements_and_adds_lengths() {
    let elab = Elaborator::default();
    for left in 0..4 {
        for right in 0..4 {
            let xs = (0..left).collect::<Vec<_>>();
            let ys = (0..right).rev().collect::<Vec<_>>();
            let mut expected = xs.clone();
            expected.extend(&ys);
            let out = elab
                .infer(&append(nat(left), nat(right), vector(&xs), vector(&ys)))
                .unwrap();
            assert_eq!(
                Kernel::default().normalize(&out.term).unwrap(),
                elab.infer(&vector(&expected)).unwrap().term
            );
            let ty = elab.infer(&E::vec(E::Nat, nat(left + right))).unwrap().term;
            Kernel::default().check(&out.term, &ty).unwrap();
        }
    }
}
#[test]
fn get_selects_every_position_for_small_vectors() {
    let elab = Elaborator::default();
    for len in 1..5 {
        let items = (0..len).rev().collect::<Vec<_>>();
        for (position, item) in items.iter().enumerate() {
            let out = elab
                .infer(&get(nat(len), vector(&items), index(len, position)))
                .unwrap();
            assert_eq!(
                Kernel::default().normalize(&out.term).unwrap(),
                elab.infer(&nat(*item)).unwrap().term
            );
        }
    }
}
#[test]
fn get_after_append_selects_elements_from_both_sides() {
    let joined = append(nat(1), nat(2), vector(&[2]), vector(&[0, 1]));
    for (position, expected) in [2, 0, 1].into_iter().enumerate() {
        let elab = Elaborator::default();
        let out = elab
            .infer(&get(nat(3), joined.clone(), index(3, position)))
            .unwrap();
        assert_eq!(
            Kernel::default().normalize(&out.term).unwrap(),
            elab.infer(&nat(expected)).unwrap().term
        );
    }
}
#[test]
fn append_nil_equation_holds_for_symbolic_length_and_vector() {
    let expr = lam(
        "m",
        E::Nat,
        lam(
            "ys",
            E::vec(E::Nat, n("m")),
            n("ys").refl().ann(E::eq(
                E::vec(E::Nat, n("m")),
                append(E::Zero, n("m"), E::vnil(E::Nat), n("ys")),
                n("ys"),
            )),
        ),
    );
    Elaborator::default().infer(&expr).unwrap();
}
#[test]
fn get_zero_equation_holds_with_symbolic_tail() {
    let lhs = get(
        n("k").succ(),
        E::vcons(E::Nat, n("k"), n("h"), n("t")),
        E::fz(n("k")),
    );
    let expr = lam(
        "k",
        E::Nat,
        lam(
            "h",
            E::Nat,
            lam(
                "t",
                E::vec(E::Nat, n("k")),
                n("h").refl().ann(E::eq(E::Nat, lhs, n("h"))),
            ),
        ),
    );
    Elaborator::default().infer(&expr).unwrap();
}
#[test]
fn get_successor_equation_recurses_on_tail_with_matching_index() {
    let lhs = get(
        n("k").succ(),
        E::vcons(E::Nat, n("k"), n("h"), n("t")),
        E::fs(n("k"), n("j")),
    );
    let rhs = get(n("k"), n("t"), n("j"));
    let expr = lam(
        "k",
        E::Nat,
        lam(
            "h",
            E::Nat,
            lam(
                "t",
                E::vec(E::Nat, n("k")),
                lam(
                    "j",
                    E::fin(n("k")),
                    rhs.clone().refl().ann(E::eq(E::Nat, lhs, rhs)),
                ),
            ),
        ),
    );
    Elaborator::default().infer(&expr).unwrap();
}
#[test]
fn operations_also_work_for_vectors_of_types() {
    let elab = Elaborator::default();
    let xs = E::vcons(E::Universe(0), E::Zero, E::Nat, E::vnil(E::Universe(0)));
    let joined = vec_append(1)
        .app(nat(1))
        .app(nat(1))
        .app(xs.clone())
        .app(xs);
    let out = elab
        .infer(&vec_get(1).app(nat(2)).app(joined).app(index(2, 1)))
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&out.term).unwrap(),
        elab.infer(&E::Nat).unwrap().term
    );
}
#[test]
fn rejects_out_of_bounds_empty_get_and_false_length_claims() {
    let elab = Elaborator::default();
    for bad in [
        get(nat(1), vector(&[0]), index(2, 1)),
        get(nat(0), vector(&[]), index(1, 0)),
        get(nat(2), vector(&[0]), index(2, 0)),
        append(nat(2), nat(0), vector(&[0]), vector(&[])),
    ] {
        assert!(elab.infer(&bad).is_err());
    }
    assert!(elab
        .check(
            &append(nat(1), nat(1), vector(&[0]), vector(&[1])),
            &E::vec(E::Nat, nat(1))
        )
        .is_err());
}
#[test]
fn invalid_prelude_levels_are_rejected_without_panicking() {
    let elab = Elaborator::default();
    assert!(elab.infer(&vec_append(u32::MAX)).is_err());
    assert!(elab.infer(&vec_get(u32::MAX)).is_err());
}
