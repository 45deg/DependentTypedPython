use deppy_core::Term;
use deppy_elab::{
    lower::Body,
    prelude::{self, structural},
    Elaborator, Error, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(name: &str) -> E {
    E::name(name)
}
#[test]
fn definitions_keep_core_references_and_infer_implicit_arguments() {
    let mut e = Elaborator::default();
    let id = e
        .define(
            "id",
            None,
            &E::lam(
                "A",
                Implicit,
                Some(E::Universe(0)),
                E::lam("x", Explicit, Some(n("A")), n("x")),
            ),
        )
        .unwrap();
    assert_eq!(e.infer(&n("id")).unwrap().term, Term::Global(id).arc());
    let out = e.infer(&n("id").app(E::Zero)).unwrap();
    assert_eq!(e.kernel().normalize(&out.term).unwrap(), Term::Zero.arc());
    e.define("zero", Some(&E::Nat), &n("id").app(E::Zero))
        .unwrap();
    e.check(&n("zero"), &E::Nat).unwrap();
}
#[test]
fn aliases_work_in_dependent_types_and_lets() {
    let mut e = Elaborator::default();
    e.define("N", Some(&E::Universe(0)), &E::Nat).unwrap();
    e.define("z", Some(&n("N")), &E::Zero).unwrap();
    e.define("empty", Some(&E::vec(n("N"), n("z"))), &E::vnil(E::Nat))
        .unwrap();
    e.check(
        &E::let_in("v", None, n("empty"), n("v")),
        &E::vec(E::Nat, E::Zero),
    )
    .unwrap();
    e.define(
        "packed",
        Some(&E::sigma("k", E::Nat, E::vec(E::Nat, n("k")))),
        &E::pair(E::Hole, n("empty")),
    )
    .unwrap();
}
#[test]
fn registration_is_atomic_and_forbids_recursive_or_duplicate_names() {
    let mut e = Elaborator::default();
    for body in [n("self"), n("future"), E::Universe(0), E::Hole] {
        assert!(e.define("self", Some(&E::Nat), &body).is_err());
        assert!(matches!(e.infer(&n("self")), Err(Error::UnknownName(_))));
    }
    assert_eq!(e.define("self", Some(&E::Nat), &E::Zero).unwrap(), 0);
    assert!(e.define("self", None, &E::Zero.succ()).is_err());
    for name in ["", "a\0b"] {
        assert!(e.define(name, None, &E::Zero).is_err());
    }
    assert_eq!(
        e.kernel()
            .normalize(&e.infer(&n("self")).unwrap().term)
            .unwrap(),
        Term::Zero.arc()
    );
}
#[test]
fn local_names_shadow_global_names() {
    let mut e = Elaborator::default();
    e.define("x", None, &E::Universe(0)).unwrap();
    let f = E::lam("x", Explicit, Some(E::Nat), n("x"));
    e.check(&f.app(E::Zero), &E::Nat).unwrap();
    e.check(&E::let_in("x", None, E::Zero, n("x")), &E::Nat)
        .unwrap();
}
#[test]
fn structural_functions_use_globals_and_can_be_registered() {
    let mut e = Elaborator::default();
    e.define("n", None, &E::Zero).unwrap(); // parameter may shadow a global
    e.define(
        "inc",
        None,
        &E::lam("x", Explicit, Some(E::Nat), n("x").succ()),
    )
    .unwrap();
    let mut f = structural::add();
    let Body::Match { arms, .. } = &mut f.body else {
        panic!()
    };
    arms[1].body = Body::Return(n("inc").app(E::Recur(vec![n("k"), n("m")])));
    let compiled = e.compile_function(&f).unwrap();
    e.define("add", None, &E::Core(compiled.term)).unwrap();
    let result = e
        .infer(&n("add").app(E::Zero.succ()).app(E::Zero.succ()))
        .unwrap();
    let expected = e
        .infer(&prelude::nat_add().app(E::Zero.succ()).app(E::Zero.succ()))
        .unwrap();
    assert!(e
        .kernel()
        .equivalent(&result.term, &expected.term, &Term::Nat.arc())
        .unwrap());
}
#[test]
fn unrelated_kernel_cannot_resolve_definition_references() {
    let mut e = Elaborator::default();
    let id = e.define("z", None, &E::Zero).unwrap();
    assert!(Elaborator::default()
        .infer(&E::Core(Term::Global(id).arc()))
        .is_err());
}
