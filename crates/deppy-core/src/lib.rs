//! Fully explicit dependent core. No Python execution, metavariables or axioms.
//! Erasure usage checking is a separate, not yet implemented phase.
mod kernel;
mod value;

pub use kernel::{Error, Kernel};
use std::sync::Arc;

pub type Tm = Arc<Term>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relevance {
    Erased,
    Runtime,
}

/// Variables use de Bruijn indices: zero denotes the nearest binder.
/// Universe levels are concrete and non-cumulative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(usize),
    Universe(u32),
    Eq {
        ty: Tm,
        left: Tm,
        right: Tm,
    },
    Refl {
        ty: Tm,
        value: Tm,
    },
    /// Based path induction: C : (y : A) -> Eq A x y -> Type[level].
    /// J A x C d y p : C y p, with J A x C d x (refl x) = d.
    J {
        level: u32,
        ty: Tm,
        left: Tm,
        motive: Tm,
        base: Tm,
        right: Tm,
        proof: Tm,
    },
    Nat,
    Zero,
    Succ(Tm),
    /// P : Nat -> Type[level], zero : P Z,
    /// step : (n : Nat) -> P n -> P (S n), result : P scrutinee.
    NatElim {
        level: u32,
        motive: Tm,
        zero: Tm,
        step: Tm,
        scrutinee: Tm,
    },
    Pi {
        relevance: Relevance,
        domain: Tm,
        codomain: Tm,
    },
    Lam {
        relevance: Relevance,
        domain: Tm,
        body: Tm,
    },
    App {
        function: Tm,
        argument: Tm,
    },
    Let {
        ty: Tm,
        value: Tm,
        body: Tm,
    },
}

impl Term {
    pub fn arc(self) -> Tm {
        Arc::new(self)
    }
}
