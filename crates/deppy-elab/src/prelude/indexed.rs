//! Indexed operations derived from the checked eliminators.
use super::{bind_lambdas, nat_add};
use crate::{
    Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(name: &str) -> E {
    E::name(name)
}
fn lambdas(names: &[&str], mut body: E) -> E {
    for name in names.iter().rev() {
        body = E::lam(*name, Explicit, None, body);
    }
    body
}

/// {A : Type[level]} -> (n m : Nat) -> Vec A n -> Vec A m -> Vec A (add n m).
/// Recursion is on the first vector's tail.
pub fn vec_append(level: u32) -> E {
    let sum = nat_add().app(n("k")).app(n("m"));
    let motive = lambdas(&["k", "rest"], E::vec(n("A"), sum.clone()));
    let cons = lambdas(
        &["k", "h", "t", "ih"],
        E::vcons(n("A"), sum, n("h"), n("ih")),
    );
    let body = E::vec_elim(level, n("A"), motive, n("ys"), cons, n("n"), n("xs"));
    bind_lambdas(
        vec![
            ("A", Implicit, E::Universe(level)),
            ("n", Explicit, E::Nat),
            ("m", Explicit, E::Nat),
            ("xs", Explicit, E::vec(n("A"), n("n"))),
            ("ys", Explicit, E::vec(n("A"), n("m"))),
        ],
        body,
    )
}

/// {A : Type[level]} -> (n : Nat) -> Vec A n -> Fin n -> A.
/// The Vec motive generalizes the later argument: P k xs = Fin k -> A.
pub fn vec_get(level: u32) -> E {
    let motive = lambdas(&["k", "rest"], E::pi("i", Explicit, E::fin(n("k")), n("A")));
    let nil = lambdas(&["i"], E::fin0_elim(n("A"), n("i")));
    let cons = lambdas(
        &["k", "h", "t", "ih", "i"],
        fin_case(level)
            .implicit(n("A"))
            .app(n("k"))
            .app(n("i"))
            .app(n("h"))
            .app(n("ih")),
    );
    let body = E::vec_elim(level, n("A"), motive, nil, cons, n("n"), n("xs")).app(n("i"));
    bind_lambdas(
        vec![
            ("A", Implicit, E::Universe(level)),
            ("n", Explicit, E::Nat),
            ("xs", Explicit, E::vec(n("A"), n("n"))),
            ("i", Explicit, E::fin(n("n"))),
        ],
        body,
    )
}

/// A non-recursive case split for Fin (S k), derived without index coercions.
/// Its motive is a type-level Nat fold:
/// M Z i = A; M (S k) i = A -> (Fin k -> A) -> A.
/// Thus both branches are typed at their own predecessor bound, even when
/// the original bound is symbolic. The Fin induction hypothesis is unused.
pub(crate) fn fin_case(level: u32) -> E {
    let choice = E::pi(
        "first",
        Explicit,
        n("A"),
        E::pi(
            "rest",
            Explicit,
            E::pi("j", Explicit, E::fin(n("k")), n("A")),
            n("A"),
        ),
    );
    // Overflow remains an explicit, invalid universe for the checker to reject.
    let family = E::nat_elim(
        level.saturating_add(1),
        lambdas(&["k"], E::Universe(level)),
        n("A"),
        lambdas(&["k", "unused"], choice),
        n("size"),
    );
    let motive = lambdas(&["size", "index"], family);
    let zero = lambdas(&["k", "first", "rest"], n("first"));
    let step = lambdas(&["k", "j", "ih", "first", "rest"], n("rest").app(n("j")));
    let body = E::fin_elim(level, motive, zero, step, n("k").succ(), n("i"))
        .app(n("first"))
        .app(n("rest"));
    bind_lambdas(
        vec![
            ("A", Implicit, E::Universe(level)),
            ("k", Explicit, E::Nat),
            ("i", Explicit, E::fin(n("k").succ())),
            ("first", Explicit, n("A")),
            (
                "rest",
                Explicit,
                E::pi("j", Explicit, E::fin(n("k")), n("A")),
            ),
        ],
        body,
    )
}

/// Dependent case analysis on Fin (S k), derived from FinElim and NatElim.
/// Generalizing the family at each successor bound avoids index coercions.
/// M (S k) i = (P : Fin (S k) -> Type[level]) -> P (FZ k) ->
///             ((j : Fin k) -> P (FS k j)) -> P i.
/// M Z i = Type[level] is unused; the fold lives one universe above P.
pub(crate) fn fin_case_dependent(level: u32) -> E {
    let family_ty = E::pi("i", Explicit, E::fin(n("k").succ()), E::Universe(level));
    let rest_ty = E::pi(
        "j",
        Explicit,
        E::fin(n("k")),
        n("P").app(E::fs(n("k"), n("j"))),
    );
    let choice = E::pi(
        "P",
        Explicit,
        family_ty.clone(),
        E::pi(
            "first",
            Explicit,
            n("P").app(E::fz(n("k"))),
            E::pi("rest", Explicit, rest_ty.clone(), n("P").app(n("index"))),
        ),
    );
    let lifted = level.saturating_add(1);
    let family = E::nat_elim(
        lifted.saturating_add(1),
        lambdas(
            &["size"],
            E::pi("index", Explicit, E::fin(n("size")), E::Universe(lifted)),
        ),
        lambdas(&["index"], E::Universe(level)),
        lambdas(&["k", "unused", "index"], choice),
        n("size"),
    );
    let motive = lambdas(&["size", "index"], family.app(n("index")));
    let zero = lambdas(&["k", "P", "first", "rest"], n("first"));
    let step = lambdas(
        &["k", "j", "ih", "P", "first", "rest"],
        n("rest").app(n("j")),
    );
    let body = E::fin_elim(lifted, motive, zero, step, n("k").succ(), n("i"))
        .app(n("P"))
        .app(n("first"))
        .app(n("rest"));
    bind_lambdas(
        vec![
            ("k", Explicit, E::Nat),
            ("P", Explicit, family_ty),
            ("i", Explicit, E::fin(n("k").succ())),
            ("first", Explicit, n("P").app(E::fz(n("k")))),
            ("rest", Explicit, rest_ty),
        ],
        body,
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn dependent_fin_case_is_kernel_checked() {
        for level in [0, 1, 2] {
            crate::Elaborator::default()
                .infer(&super::fin_case_dependent(level))
                .unwrap();
        }
    }
}
