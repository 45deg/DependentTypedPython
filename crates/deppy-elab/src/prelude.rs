//! Fixed definitions expressed in the input language, not trusted axioms.
//! Call `Elaborator::infer` to elaborate and kernel-check each definition.
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
