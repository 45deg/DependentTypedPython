//! Conservative elaboration of a named, programmatic input AST.
//!
//! This is not a Python parser. Each operation owns its metavariables; success
//! returns only fully explicit terms independently rechecked by deppy-core.
mod data;
pub mod lower;
pub mod prelude;
pub use data::{NamedConstructor, NamedDataDecl};
mod record;
mod solve;
pub use record::{Record, RecordDecl};
mod syntax;

use deppy_core::{Kernel, Tm};
use solve::{Context, State};
use std::fmt;
pub use syntax::{Expr, Plicity};

pub type SourceId = String;

/// Source identity and UTF-8 byte offsets; absent from trusted core terms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLocation {
    pub source: SourceId,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoalLocal {
    pub name: String,
    pub ty: String,
    pub value: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Goal {
    pub id: usize,
    pub name: String,
    pub location: Option<SourceLocation>,
    pub context: Vec<GoalLocal>,
    pub expected: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// Context for a failed type-shape or unification check, retaining its cause.
    WithTypes {
        expected: String,
        actual: String,
        error: Box<Error>,
    },
    TypeMismatch {
        expected: String,
        actual: String,
    },
    Goals(Vec<Goal>),
    Located {
        location: SourceLocation,
        error: Box<Error>,
    },
    InvalidRecursion(String),
    InvalidPattern(String),
    UnsupportedMatch(String),
    UnknownName(String),
    InvalidDeclarationName(String),
    AnnotationRequired,
    ExpectedUniverse,
    ExpectedFunction,
    ExpectedSigma,
    ExpectedRecord,
    ExpectedInductive,
    PlicityMismatch,
    CannotUnify,
    OccursCheck,
    ScopeEscape,
    NonPattern,
    UnsolvedMeta {
        id: usize,
    },
    UniverseOverflow,
    BudgetExceeded,
    Kernel(deppy_core::Error),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeMismatch { expected, actual } => {
                write!(f, "expected {expected}, got {actual}")
            }
            Self::Goals(goals) => write!(f, "{} unfinished proof goal(s)", goals.len()),
            Self::Located { error, .. } => error.fmt(f),
            Self::WithTypes {
                expected,
                actual,
                error,
            } => write!(f, "{error}: expected {expected}, got {actual}"),
            Self::InvalidRecursion(reason) => write!(f, "invalid structural recursion: {reason}"),
            Self::InvalidPattern(reason) => write!(f, "invalid pattern: {reason}"),
            Self::UnsupportedMatch(reason) => write!(f, "unsupported match: {reason}"),
            Self::InvalidDeclarationName(name) => {
                write!(f, "empty or duplicate declaration name: {name}")
            }
            Self::UnknownName(name) => write!(f, "unknown name: {name}"),
            Self::AnnotationRequired => write!(f, "a type annotation or expected type is required"),
            Self::ExpectedUniverse => {
                write!(f, "expected a concrete universe; add a type annotation")
            }
            Self::ExpectedInductive => write!(f, "expected an inductive family"),
            Self::ExpectedRecord => write!(f, "expected a known nominal record type"),
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
impl Error {
    pub fn cause(&self) -> &Self {
        match self {
            Self::Located { error, .. } | Self::WithTypes { error, .. } => error.cause(),
            error => error,
        }
    }
    pub fn type_details(&self) -> Option<(&str, &str)> {
        match self {
            Self::Located { error, .. } => error.type_details(),
            Self::WithTypes {
                expected, actual, ..
            }
            | Self::TypeMismatch { expected, actual } => Some((expected, actual)),
            _ => None,
        }
    }
    pub fn at(self, location: &SourceLocation) -> Self {
        if matches!(self, Self::Located { .. }) {
            self
        } else {
            Self::Located {
                location: location.clone(),
                error: Box::new(self),
            }
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
#[derive(Clone)]
pub struct Elaborator {
    kernel: Kernel,
    max_steps: usize,
    globals: std::collections::HashMap<String, deppy_core::DefId>,
    next_definition: deppy_core::DefId,
    records: std::collections::HashMap<deppy_core::InductiveId, Record>,
}
impl Default for Elaborator {
    fn default() -> Self {
        Self::new(100_000)
    }
}
impl Elaborator {
    /// Elaboration and each independent kernel recheck use this step limit.
    pub fn new(max_steps: usize) -> Self {
        Self {
            max_steps,
            globals: Default::default(),
            next_definition: 0,
            records: Default::default(),
            kernel: Kernel::new(max_steps),
        }
    }

    /// Register a checked transparent definition. Registration is atomic and names
    /// are immutable; local binders take precedence during name resolution.
    pub fn define(
        &mut self,
        name: impl Into<String>,
        ty: Option<&Expr>,
        body: &Expr,
    ) -> Result<deppy_core::DefId, Error> {
        self.define_with_transparency(name, ty, body, false)
    }

    pub fn define_opaque(
        &mut self,
        name: impl Into<String>,
        ty: Option<&Expr>,
        body: &Expr,
    ) -> Result<deppy_core::DefId, Error> {
        self.define_with_transparency(name, ty, body, true)
    }

    fn define_with_transparency(
        &mut self,
        name: impl Into<String>,
        ty: Option<&Expr>,
        body: &Expr,
        opaque: bool,
    ) -> Result<deppy_core::DefId, Error> {
        let name = name.into();
        if name.is_empty() || name.contains('\0') || self.globals.contains_key(&name) {
            return Err(Error::InvalidDeclarationName(name));
        }
        let next = self
            .next_definition
            .checked_add(1)
            .ok_or(Error::BudgetExceeded)?;
        let out = if let Some(ty) = ty {
            self.check(body, ty)?
        } else {
            self.infer(body)?
        };
        let id = self.next_definition;
        let definition = deppy_core::Definition {
            ty: out.ty,
            body: out.term,
        };
        if opaque {
            self.kernel.define_opaque(id, definition)?;
        } else {
            self.kernel.define(id, definition)?;
        }
        self.globals.insert(name, id);
        self.next_definition = next;
        Ok(id)
    }

    /// Declare an opaque assumption; this never treats an unsolved meta as evidence.
    pub fn declare_axiom(
        &mut self,
        name: impl Into<String>,
        ty: &Expr,
    ) -> Result<deppy_core::DefId, Error> {
        let name = name.into();
        if name.is_empty() || name.contains('\0') || self.globals.contains_key(&name) {
            return Err(Error::InvalidDeclarationName(name));
        }
        let next = self
            .next_definition
            .checked_add(1)
            .ok_or(Error::BudgetExceeded)?;
        let out = self.infer(ty)?;
        let id = self.next_definition;
        self.kernel.declare_axiom(id, out.term)?;
        self.globals.insert(name, id);
        self.next_definition = next;
        Ok(id)
    }

    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }
    pub fn infer(&self, expr: &Expr) -> Result<Elaborated, Error> {
        let mut state = State::with_kernel(self.max_steps, self.kernel.clone());
        state.globals = self.globals.clone();
        state.records = self.records.clone();
        let (term, ty) = state.synth(&Context::new(), expr)?;
        state.finish(term, ty, &self.kernel)
    }

    pub fn check(&self, expr: &Expr, expected: &Expr) -> Result<Elaborated, Error> {
        let mut state = State::with_kernel(self.max_steps, self.kernel.clone());
        state.globals = self.globals.clone();
        state.records = self.records.clone();
        let ctx = Context::new();
        let (ty, _) = state.type_expr(&ctx, expected)?;
        let term = state.check(&ctx, expr, &ty)?;
        state.finish(term, ty, &self.kernel)
    }
}
