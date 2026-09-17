//! Fixed definitions expressed in the input language, not trusted axioms.
//! Call `Elaborator::infer` to elaborate and kernel-check each definition.
mod indexed;
pub use indexed::{vec_append, vec_get};

use crate::{Expr as E, Plicity::Explicit};

/// add : Nat -> Nat -> Nat, recursing on the first argument.
/// add Z m = m; add (S k) m = S (add k m).
pub fn nat_add() -> E {
    E::lam(
        "n",
        Explicit,
        Some(E::Nat),
        E::lam(
            "m",
            Explicit,
            Some(E::Nat),
            E::nat_elim(
                0,
                E::lam("k", Explicit, Some(E::Nat), E::Nat),
                E::name("m"),
                E::lam(
                    "k",
                    Explicit,
                    Some(E::Nat),
                    E::lam("ih", Explicit, Some(E::Nat), E::name("ih").succ()),
                ),
                E::name("n"),
            ),
        ),
    )
}

/// Congruence derived from J, with concrete source and target universe levels.
/// {A : Type[u]} -> {B : Type[v]} -> (f : A -> B) ->
/// {x : A} -> {y : A} -> Eq A x y -> Eq B (f x) (f y).
pub fn cong(source_level: u32, target_level: u32) -> E {
    use crate::Plicity::Implicit;
    let n = E::name;
    let motive = E::lam(
        "z",
        Explicit,
        None,
        E::lam(
            "q",
            Explicit,
            None,
            E::eq(n("B"), n("f").app(n("x")), n("f").app(n("z"))),
        ),
    );
    let body = E::j(
        target_level,
        n("A"),
        n("x"),
        motive,
        n("f").app(n("x")).refl(),
        n("y"),
        n("p"),
    );
    bind_lambdas(
        vec![
            ("A", Implicit, E::Universe(source_level)),
            ("B", Implicit, E::Universe(target_level)),
            ("f", Explicit, E::pi("arg", Explicit, n("A"), n("B"))),
            ("x", Implicit, n("A")),
            ("y", Implicit, n("A")),
            ("p", Explicit, E::eq(n("A"), n("x"), n("y"))),
        ],
        body,
    )
}

/// Transport derived from J: {A} -> (P : A -> Type[v]) -> {x y : A} ->
/// Eq A x y -> P x -> P y. This is a logical definition, with no runtime erasure.
pub fn transport(carrier_level: u32, family_level: u32) -> E {
    use crate::Plicity::Implicit;
    let n = E::name;
    let motive = E::lam(
        "z",
        Explicit,
        None,
        E::lam("q", Explicit, None, n("P").app(n("z"))),
    );
    let body = E::j(
        family_level,
        n("A"),
        n("x"),
        motive,
        n("value"),
        n("y"),
        n("p"),
    );
    bind_lambdas(
        vec![
            ("A", Implicit, E::Universe(carrier_level)),
            (
                "P",
                Explicit,
                E::pi("arg", Explicit, n("A"), E::Universe(family_level)),
            ),
            ("x", Implicit, n("A")),
            ("y", Implicit, n("A")),
            ("p", Explicit, E::eq(n("A"), n("x"), n("y"))),
            ("value", Explicit, n("P").app(n("x"))),
        ],
        body,
    )
}

/// Induction proof of (n : Nat) -> Eq Nat (add n Z) n.
/// The successor branch applies congruence to the induction hypothesis.
pub fn zero_right() -> E {
    let n = E::name;
    let motive = E::lam(
        "k",
        Explicit,
        None,
        E::eq(E::Nat, nat_add().app(n("k")).app(E::Zero), n("k")),
    );
    let successor = E::lam("a", Explicit, Some(E::Nat), n("a").succ());
    let step = E::lam(
        "k",
        Explicit,
        None,
        E::lam("ih", Explicit, None, cong(0, 0).app(successor).app(n("ih"))),
    );
    E::lam(
        "n",
        Explicit,
        Some(E::Nat),
        E::nat_elim(0, motive, E::Zero.refl(), step, n("n")),
    )
}

fn bind_lambdas(binders: Vec<(&str, crate::Plicity, E)>, mut body: E) -> E {
    for (name, plicity, domain) in binders.into_iter().rev() {
        body = E::lam(name, plicity, Some(domain), body);
    }
    body
}
