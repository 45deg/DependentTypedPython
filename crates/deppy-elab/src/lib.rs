//! Conservative elaboration of a named, programmatic input AST.
//!
//! This is not a Python parser. Each operation owns its metavariables; success
//! returns only fully explicit terms independently rechecked by deppy-core.
pub mod prelude;
mod solve;
mod syntax;

use deppy_core::{Kernel, Tm};
use solve::{Context, State};
use std::fmt;
pub use syntax::{Expr, Plicity};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnknownName(String),
    AnnotationRequired,
    ExpectedUniverse,
    ExpectedFunction,
    ExpectedSigma,
    PlicityMismatch,
    CannotUnify,
    OccursCheck,
    ScopeEscape,
    NonPattern,
    UnsolvedMeta { id: usize },
    UniverseOverflow,
    BudgetExceeded,
    Kernel(deppy_core::Error),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownName(name) => write!(f, "unknown name: {name}"),
            Self::AnnotationRequired => write!(f, "a type annotation or expected type is required"),
            Self::ExpectedUniverse => {
                write!(f, "expected a concrete universe; add a type annotation")
            }
            Self::ExpectedSigma => write!(f, "expected a known dependent pair type"),
            Self::ExpectedFunction => write!(f, "expected a known dependent function type"),
            Self::PlicityMismatch => write!(f, "explicit/implicit argument mismatch"),
            Self::CannotUnify => write!(f, "types do not unify in the supported fragment"),
            Self::OccursCheck => write!(f, "cyclic metavariable solution"),
            Self::ScopeEscape => write!(
                f,
                "metavariable solution refers to a variable outside its scope"
            ),
            Self::NonPattern => {
                write!(f, "metavariable arguments must be distinct local variables")
            }
            Self::UnsolvedMeta { id } => write!(
                f,
                "unsolved metavariable {id}; add an explicit argument or annotation"
            ),
            Self::UniverseOverflow => write!(f, "universe level exceeds the supported range"),
            Self::BudgetExceeded => write!(f, "elaboration budget exhausted; result is unknown"),
            Self::Kernel(error) => write!(f, "kernel recheck failed: {error}"),
        }
    }
}
impl std::error::Error for Error {}
impl From<deppy_core::Error> for Error {
    fn from(error: deppy_core::Error) -> Self {
        Self::Kernel(error)
    }
}

#[derive(Clone, Debug)]
pub struct Elaborated {
    pub term: Tm,
    pub ty: Tm,
}

/// No mutable inference state is retained between operations.
pub struct Elaborator {
    max_steps: usize,
}
impl Default for Elaborator {
    fn default() -> Self {
        Self::new(100_000)
    }
}
impl Elaborator {
    /// Elaboration and each independent kernel recheck use this step limit.
    pub fn new(max_steps: usize) -> Self {
        Self { max_steps }
    }

    pub fn infer(&self, expr: &Expr) -> Result<Elaborated, Error> {
        let mut state = State::new(self.max_steps);
        let (term, ty) = state.synth(&Context::new(), expr)?;
        state.finish(term, ty, &Kernel::new(self.max_steps))
    }

    pub fn check(&self, expr: &Expr, expected: &Expr) -> Result<Elaborated, Error> {
        let mut state = State::new(self.max_steps);
        let ctx = Context::new();
        let (ty, _) = state.type_expr(&ctx, expected)?;
        let term = state.check(&ctx, expr, &ty)?;
        state.finish(term, ty, &Kernel::new(self.max_steps))
    }
}
