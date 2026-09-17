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
    Nat,
    Zero,
    Succ(Tm),
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
