use deppy_core::Relevance;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Plicity {
    Explicit,
    Implicit,
}
impl Plicity {
    pub(crate) fn relevance(self) -> Relevance {
        match self {
            Self::Explicit => Relevance::Runtime,
            Self::Implicit => Relevance::Erased,
        }
    }
}

/// Named input to elaboration. `Hole` can only be checked against a known type.
/// Implicit binders are erased; explicit erased proof binders are not yet exposed.
#[derive(Clone, Debug)]
pub enum Expr {
    Name(String),
    Universe(u32),
    Pi {
        name: String,
        plicity: Plicity,
        domain: Box<Expr>,
        codomain: Box<Expr>,
    },
    Lam {
        name: String,
        plicity: Plicity,
        domain: Option<Box<Expr>>,
        body: Box<Expr>,
    },
    App {
        function: Box<Expr>,
        argument: Box<Expr>,
        plicity: Plicity,
    },
    Ann {
        term: Box<Expr>,
        ty: Box<Expr>,
    },
    Hole,
}
impl Expr {
    pub fn name(name: impl Into<String>) -> Self {
        Self::Name(name.into())
    }
    pub fn pi(name: impl Into<String>, plicity: Plicity, domain: Self, codomain: Self) -> Self {
        Self::Pi {
            name: name.into(),
            plicity,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }
    pub fn lam(
        name: impl Into<String>,
        plicity: Plicity,
        domain: Option<Self>,
        body: Self,
    ) -> Self {
        Self::Lam {
            name: name.into(),
            plicity,
            domain: domain.map(Box::new),
            body: Box::new(body),
        }
    }
    pub fn app(self, argument: Self) -> Self {
        Self::App {
            function: Box::new(self),
            argument: Box::new(argument),
            plicity: Plicity::Explicit,
        }
    }
    /// Positional explicit specification of an otherwise implicit argument.
    pub fn implicit(self, argument: Self) -> Self {
        Self::App {
            function: Box::new(self),
            argument: Box::new(argument),
            plicity: Plicity::Implicit,
        }
    }
    pub fn ann(self, ty: Self) -> Self {
        Self::Ann {
            term: Box::new(self),
            ty: Box::new(ty),
        }
    }
}

pub(crate) type Id = usize;
pub(crate) type T = Arc<Term>;

/// Separate from the trusted core. Binders have fresh identities; meta spines
/// explicitly instantiate the telescope captured when the meta was created.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Term {
    Local(Id),
    Universe(u32),
    Pi {
        id: Id,
        plicity: Plicity,
        domain: T,
        body: T,
    },
    Lam {
        id: Id,
        plicity: Plicity,
        domain: T,
        body: T,
    },
    App(T, T),
    Meta(Id, Vec<T>),
}
impl Term {
    pub fn arc(self) -> T {
        Arc::new(self)
    }
}
