use crate::syntax::{Id, Term, T};
use crate::{Elaborated, Error, Expr, Plicity};
use deppy_core::{Kernel, Term as Core, Tm};
use std::collections::{HashMap, HashSet};

mod cases;
mod core;
mod infer;
mod state;
mod term_ops;
mod unify;

pub(crate) use state::{Context, State};

fn pi(id: Id, domain: T, body: T) -> T {
    Term::Pi {
        id,
        plicity: Plicity::Explicit,
        domain,
        body,
    }
    .arc()
}
fn app2(f: T, a: T, b: T) -> T {
    Term::App(Term::App(f, a).arc(), b).arc()
}

#[cfg(test)]
mod tests;
