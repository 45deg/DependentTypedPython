use deppy_core::{Kernel, Term as C, Tm};
use deppy_elab::{
    prelude::nat_add,
    Elaborator, Error, Expr as E,
    Plicity::{Explicit as X, Implicit as I},
};
fn name(s: &str) -> E {
    E::name(s)
}
fn lam(s: &str, ty: E, body: E) -> E {
    E::lam(s, X, Some(ty), body)
}
fn pi(s: &str, ty: E, body: E) -> E {
    E::pi(s, X, ty, body)
}
fn numeral(n: usize) -> E {
    (0..n).fold(E::Zero, |n, _| n.succ())
}
fn core_num(n: usize) -> Tm {
    (0..n).fold(C::Zero.arc(), |n, _| C::Succ(n).arc())
}
fn nf(expr: &E) -> Tm {
    let result = Elaborator::default().infer(expr).unwrap();
    Kernel::default().normalize(&result.term).unwrap()
}
fn rec(motive: E, zero: E, step: E, n: E) -> E {
    E::nat_elim(0, motive, zero, step, n)
}
fn step() -> E {
    E::lam("k", X, None, E::lam("ih", X, None, name("ih").succ()))
}

#[test]
fn identity_infers_nat_for_zero() {
    let id = E::lam("A", I, Some(E::Universe(0)), lam("x", name("A"), name("x")));
    let result = Elaborator::default().infer(&id.app(E::Zero)).unwrap();
    assert_eq!(result.ty, C::Nat.arc());
    assert_eq!(
        Kernel::default().normalize(&result.term).unwrap(),
        C::Zero.arc()
    );
    let C::App { function, .. } = result.term.as_ref() else {
        panic!()
    };
    let C::App { argument, .. } = function.as_ref() else {
        panic!()
    };
    assert_eq!(argument.as_ref(), &C::Nat);
}
#[test]
fn infer_implicit_natural_index_from_a_type_family() {
    // Under F : Nat -> Type0, x : F Z, infer n=Z in f[n](x).
    let fty = E::pi(
        "n",
        I,
        E::Nat,
        pi("value", name("F").app(name("n")), name("F").app(name("n"))),
    );
    let expr = lam(
        "F",
        pi("n", E::Nat, E::Universe(0)),
        lam(
            "x",
            name("F").app(E::Zero),
            lam("f", fty, name("f").app(name("x"))),
        ),
    );
    let result = Elaborator::default().infer(&expr).unwrap();
    Kernel::default().check(&result.term, &result.ty).unwrap();
    let C::Lam { body, .. } = result.term.as_ref() else {
        panic!()
    };
    let C::Lam { body, .. } = body.as_ref() else {
        panic!()
    };
    let C::Lam { body, .. } = body.as_ref() else {
        panic!()
    };
    let C::App { function, .. } = body.as_ref() else {
        panic!()
    };
    let C::App { argument, .. } = function.as_ref() else {
        panic!()
    };
    assert_eq!(argument.as_ref(), &C::Zero);
}
#[test]
fn concrete_addition_table() {
    for a in 0..5 {
        for b in 0..5 {
            assert_eq!(
                nf(&nat_add().app(numeral(a)).app(numeral(b))),
                core_num(a + b)
            );
        }
    }
}
#[test]
fn addition_type_is_nat_to_nat_to_nat() {
    let result = Elaborator::default().infer(&nat_add()).unwrap();
    let expected = Elaborator::default()
        .infer(&pi("n", E::Nat, pi("m", E::Nat, E::Nat)))
        .unwrap();
    assert_eq!(
        Kernel::default().normalize(&result.ty).unwrap(),
        expected.term
    );
}
#[test]
fn zero_left_reduces_but_zero_right_is_not_definitionally_equal() {
    let left = lam("n", E::Nat, nat_add().app(E::Zero).app(name("n")));
    let right = lam("n", E::Nat, nat_add().app(name("n")).app(E::Zero));
    let identity = lam("n", E::Nat, name("n"));
    assert_eq!(nf(&left), nf(&identity));
    let right = Elaborator::default().infer(&right).unwrap();
    let identity = Elaborator::default().infer(&identity).unwrap();
    assert!(!Kernel::default()
        .equivalent(&right.term, &identity.term, &identity.ty)
        .unwrap());
}
#[test]
fn successor_equation_holds_with_symbolic_arguments() {
    let left = lam(
        "n",
        E::Nat,
        lam("m", E::Nat, nat_add().app(name("n").succ()).app(name("m"))),
    );
    let right = lam(
        "n",
        E::Nat,
        lam("m", E::Nat, nat_add().app(name("n")).app(name("m")).succ()),
    );
    assert_eq!(nf(&left), nf(&right));
}
fn indexed_annotation(index: E) -> E {
    lam(
        "F",
        pi("k", E::Nat, E::Universe(0)),
        lam(
            "n",
            E::Nat,
            lam(
                "x",
                name("F").app(name("n")),
                name("x").ann(name("F").app(index)),
            ),
        ),
    )
}
#[test]
fn elaboration_reduces_addition_in_dependent_annotations() {
    let expr = indexed_annotation(nat_add().app(E::Zero).app(name("n")));
    Elaborator::default().infer(&expr).unwrap();
}
#[test]
fn rejects_zero_right_as_a_definitional_conversion() {
    let expr = indexed_annotation(nat_add().app(name("n")).app(E::Zero));
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::CannotUnify)
    ));
}
#[test]
fn constructor_meta_is_solved_inside_successor_index() {
    let fty = E::pi(
        "n",
        I,
        E::Nat,
        pi("x", name("F").app(name("n").succ()), E::Nat),
    );
    let expr = lam(
        "F",
        pi("k", E::Nat, E::Universe(0)),
        lam(
            "x",
            name("F").app(E::Zero.succ()),
            lam("f", fty, name("f").app(name("x"))),
        ),
    );
    Elaborator::default().infer(&expr).unwrap();
}
#[test]
fn expected_types_fill_motive_and_branch_lambda_annotations() {
    let expr = rec(E::lam("n", X, None, E::Nat), E::Zero, step(), numeral(3));
    assert_eq!(nf(&expr), core_num(3));
}
// P Z = Nat; P (S k) = Nat -> Nat.
fn family() -> E {
    lam(
        "n",
        E::Nat,
        E::nat_elim(
            1,
            E::lam("k", X, None, E::Universe(0)),
            E::Nat,
            E::lam("k", X, None, E::lam("ih", X, None, pi("x", E::Nat, E::Nat))),
            name("n"),
        ),
    )
}
#[test]
fn dependent_elimination_changes_result_type() {
    let branch = E::lam(
        "k",
        X,
        None,
        E::lam("ih", X, None, E::lam("x", X, None, name("x"))),
    );
    for (n, expected) in [(E::Zero, E::Nat), (E::Zero.succ(), pi("x", E::Nat, E::Nat))] {
        let result = Elaborator::default()
            .infer(&rec(family(), E::Zero, branch.clone(), n))
            .unwrap();
        let expected = Elaborator::default().infer(&expected).unwrap();
        assert_eq!(
            Kernel::default().normalize(&result.ty).unwrap(),
            expected.term
        );
    }
}
#[test]
fn rejects_invalid_constructors_and_branch_types() {
    for expr in [
        E::Nat.succ(),
        E::Universe(0).succ(),
        rec(lam("n", E::Nat, E::Nat), E::Nat, step(), E::Zero),
        rec(
            lam("n", E::Nat, E::Nat),
            E::Zero,
            lam("k", E::Nat, lam("ih", E::Nat, E::Nat)),
            E::Zero,
        ),
        rec(lam("n", E::Nat, E::Nat), E::Zero, step(), E::Nat),
    ] {
        assert!(Elaborator::default().infer(&expr).is_err());
    }
}
#[test]
fn rejects_wrong_motive_and_universe_level() {
    for expr in [
        rec(lam("n", E::Nat, E::Zero), E::Zero, step(), E::Zero),
        rec(lam("n", E::Nat, E::Universe(0)), E::Nat, step(), E::Zero),
        E::nat_elim(u32::MAX, lam("n", E::Nat, E::Nat), E::Zero, step(), E::Zero),
    ] {
        assert!(Elaborator::default().infer(&expr).is_err());
    }
}
#[test]
fn rejects_wrong_dependent_hypothesis() {
    let branch = lam("k", E::Nat, lam("ih", E::Nat, lam("x", E::Nat, name("x"))));
    assert!(Elaborator::default()
        .infer(&rec(family(), E::Zero, branch, E::Zero))
        .is_err());
}
#[test]
fn unresolved_holes_in_unused_branches_are_not_erased() {
    let expr = rec(lam("n", E::Nat, E::Nat), E::Zero, E::Hole, E::Zero);
    assert!(matches!(
        Elaborator::default().infer(&expr),
        Err(Error::UnsolvedMeta { .. })
    ));
}
#[test]
fn rejects_partial_functions_and_unbounded_elaboration() {
    let bogus = rec(
        lam("n", E::Nat, E::Nat),
        E::Zero,
        lam(
            "k",
            E::Nat,
            lam("ih", E::Nat, name("recurse").app(name("k"))),
        ),
        E::Zero,
    );
    assert!(matches!(
        Elaborator::default().infer(&bogus),
        Err(Error::UnknownName(_))
    ));
    assert!(matches!(
        Elaborator::new(20).infer(&nat_add()),
        Err(Error::BudgetExceeded)
    ));
}
