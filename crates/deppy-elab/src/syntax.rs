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
    /// Equality rewriting, elaborated to J; no new kernel primitive.
    Rewrite {
        proof: Box<Expr>,
        body: Box<Expr>,
        forward: bool,
    },
    /// Type-directed constructor splitting. It elaborates entirely to checked
    /// inductive eliminators and introduces no new core computation rules.
    Cases {
        level: u32,
        value: Box<Expr>,
        branches: Vec<CaseBranch>,
        generalize: Vec<(String, Expr)>,
    },
    Absurd {
        ty: Box<Expr>,
        value: Box<Expr>,
    },
    Induct {
        level: u32,
        value: Box<Expr>,
        motive: Box<Expr>,
        branches: Vec<Expr>,
    },
    UserHole(String),
    /// Bounded proof search using only context evidence and explicit checked hints.
    /// Failure leaves a named user goal; no search primitive reaches the kernel.
    AutoProof {
        name: String,
        hints: Vec<String>,
    },
    Located {
        location: crate::SourceLocation,
        expression: Box<Expr>,
    },
    /// Immutable local definition; the value is outside the new binding's scope.
    Let {
        name: String,
        ty: Option<Box<Expr>>,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    /// A self-call in function HIR; all declared arguments, including implicit ones, are required.
    /// Only `compile_function`/`lower_function` may eliminate this node.
    Recur(Vec<Expr>),

    /// Embed a closed explicit term, independently checked in this elaborator's kernel.
    Core(deppy_core::Tm),

    Sigma {
        name: String,
        domain: Box<Expr>,
        codomain: Box<Expr>,
    },
    Pair {
        fst: Box<Expr>,
        snd: Box<Expr>,
    },
    /// Resolve a named record projection from the inferred nominal receiver type.
    RecordElim {
        level: u32,
        motive: Box<Expr>,
        branch: Box<Expr>,
        value: Box<Expr>,
    },
    Field {
        value: Box<Expr>,
        name: String,
    },
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    Name(String),
    Universe(u32),
    Eq {
        ty: Box<Expr>,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Refl(Box<Expr>),
    J {
        level: u32,
        ty: Box<Expr>,
        left: Box<Expr>,
        motive: Box<Expr>,
        base: Box<Expr>,
        right: Box<Expr>,
        proof: Box<Expr>,
    },
    Vec {
        ty: Box<Expr>,
        len: Box<Expr>,
    },
    VNil {
        ty: Box<Expr>,
    },
    VCons {
        ty: Box<Expr>,
        len: Box<Expr>,
        head: Box<Expr>,
        tail: Box<Expr>,
    },
    Fin {
        bound: Box<Expr>,
    },
    FZ {
        bound: Box<Expr>,
    },
    FS {
        bound: Box<Expr>,
        pred: Box<Expr>,
    },
    VecElim {
        level: u32,
        ty: Box<Expr>,
        motive: Box<Expr>,
        nil: Box<Expr>,
        cons: Box<Expr>,
        len: Box<Expr>,
        scrutinee: Box<Expr>,
    },
    FinElim {
        level: u32,
        motive: Box<Expr>,
        zero: Box<Expr>,
        step: Box<Expr>,
        bound: Box<Expr>,
        scrutinee: Box<Expr>,
    },
    Fin0Elim {
        ty: Box<Expr>,
        absurd: Box<Expr>,
    },
    Nat,
    Zero,
    Succ(Box<Expr>),
    NatElim {
        level: u32,
        motive: Box<Expr>,
        zero: Box<Expr>,
        step: Box<Expr>,
        scrutinee: Box<Expr>,
    },
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

#[derive(Clone, Debug)]
pub struct CaseBranch {
    pub constructor: CaseConstructor,
    pub fields: Vec<String>,
    pub body: Expr,
    pub location: Option<crate::SourceLocation>,
}
#[derive(Clone, Debug)]
pub enum CaseConstructor {
    Name(String),
    Core(u64, usize),
}
impl From<String> for CaseConstructor {
    fn from(name: String) -> Self {
        Self::Name(name)
    }
}
impl Expr {
    pub(crate) fn contains_recur(&self) -> bool {
        self.any(&|e| matches!(e, Expr::Recur(_)))
    }
    pub(crate) fn any(&self, predicate: &impl Fn(&Expr) -> bool) -> bool {
        if predicate(self) {
            return true;
        }
        use Expr::*;
        let children: std::vec::Vec<&Expr> = match self {
            Rewrite { proof, body, .. } => vec![proof, body],
            Recur(arguments) => arguments.iter().collect(),
            Core(_)
            | Name(_)
            | Universe(_)
            | Nat
            | Zero
            | Hole
            | UserHole(_)
            | AutoProof { .. } => vec![],
            Located { expression, .. } => vec![expression],
            Fst(x)
            | Snd(x)
            | Refl(x)
            | Succ(x)
            | VNil { ty: x }
            | Fin { bound: x }
            | FZ { bound: x }
            | Field { value: x, .. } => vec![x],
            Absurd { ty, value } | Ann { ty, term: value } => vec![ty, value],
            App {
                function, argument, ..
            } => vec![function, argument],
            Sigma {
                domain, codomain, ..
            }
            | Pi {
                domain, codomain, ..
            } => vec![domain, codomain],
            Pair { fst, snd } => vec![fst, snd],
            Vec { ty, len } => vec![ty, len],
            FS { bound, pred } => vec![bound, pred],
            Fin0Elim { ty, absurd } => vec![ty, absurd],
            Let {
                ty, value, body, ..
            } => ty
                .iter()
                .map(Box::as_ref)
                .chain([value.as_ref(), body.as_ref()])
                .collect(),
            Lam { domain, body, .. } => domain
                .iter()
                .map(Box::as_ref)
                .chain([body.as_ref()])
                .collect(),
            Eq { ty, left, right } => vec![ty, left, right],
            RecordElim {
                motive,
                branch,
                value,
                ..
            } => vec![motive, branch, value],
            VCons {
                ty,
                len,
                head,
                tail,
            } => vec![ty, len, head, tail],
            NatElim {
                motive,
                zero,
                step,
                scrutinee,
                ..
            } => vec![motive, zero, step, scrutinee],
            FinElim {
                motive,
                zero,
                step,
                bound,
                scrutinee,
                ..
            } => vec![motive, zero, step, bound, scrutinee],
            VecElim {
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
                ..
            } => vec![ty, motive, nil, cons, len, scrutinee],
            J {
                ty,
                left,
                motive,
                base,
                right,
                proof,
                ..
            } => vec![ty, left, motive, base, right, proof],
            Induct {
                value,
                motive,
                branches,
                ..
            } => [value.as_ref(), motive.as_ref()]
                .into_iter()
                .chain(branches)
                .collect(),
            Cases {
                value,
                branches,
                generalize,
                ..
            } => [value.as_ref()]
                .into_iter()
                .chain(branches.iter().map(|b| &b.body))
                .chain(generalize.iter().map(|(_, e)| e))
                .collect(),
        };
        children.into_iter().any(|e| e.any(predicate))
    }
    pub fn located(self, location: crate::SourceLocation) -> Self {
        Self::Located {
            location,
            expression: Box::new(self),
        }
    }
    pub fn unlocated(&self) -> &Self {
        match self {
            Self::Located { expression, .. } => expression.unlocated(),
            other => other,
        }
    }

    pub fn field(self, name: impl Into<String>) -> Self {
        Self::Field {
            value: Box::new(self),
            name: name.into(),
        }
    }

    pub fn let_in(name: impl Into<String>, ty: Option<Self>, value: Self, body: Self) -> Self {
        Self::Let {
            name: name.into(),
            ty: ty.map(Box::new),
            value: Box::new(value),
            body: Box::new(body),
        }
    }

    pub fn sigma(name: impl Into<String>, domain: Self, codomain: Self) -> Self {
        Self::Sigma {
            name: name.into(),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }
    pub fn pair(fst: Self, snd: Self) -> Self {
        Self::Pair {
            fst: Box::new(fst),
            snd: Box::new(snd),
        }
    }
    pub fn fst(self) -> Self {
        Self::Fst(Box::new(self))
    }
    pub fn snd(self) -> Self {
        Self::Snd(Box::new(self))
    }

    pub fn vec(ty: Self, len: Self) -> Self {
        Self::Vec {
            ty: Box::new(ty),
            len: Box::new(len),
        }
    }
    pub fn vnil(ty: Self) -> Self {
        Self::VNil { ty: Box::new(ty) }
    }
    pub fn vcons(ty: Self, len: Self, head: Self, tail: Self) -> Self {
        Self::VCons {
            ty: Box::new(ty),
            len: Box::new(len),
            head: Box::new(head),
            tail: Box::new(tail),
        }
    }
    pub fn fin(bound: Self) -> Self {
        Self::Fin {
            bound: Box::new(bound),
        }
    }
    pub fn fz(bound: Self) -> Self {
        Self::FZ {
            bound: Box::new(bound),
        }
    }
    pub fn fs(bound: Self, pred: Self) -> Self {
        Self::FS {
            bound: Box::new(bound),
            pred: Box::new(pred),
        }
    }
    pub fn vec_elim(
        level: u32,
        ty: Self,
        motive: Self,
        nil: Self,
        cons: Self,
        len: Self,
        scrutinee: Self,
    ) -> Self {
        Self::VecElim {
            level,
            ty: Box::new(ty),
            motive: Box::new(motive),
            nil: Box::new(nil),
            cons: Box::new(cons),
            len: Box::new(len),
            scrutinee: Box::new(scrutinee),
        }
    }
    pub fn fin_elim(
        level: u32,
        motive: Self,
        zero: Self,
        step: Self,
        bound: Self,
        scrutinee: Self,
    ) -> Self {
        Self::FinElim {
            level,
            motive: Box::new(motive),
            zero: Box::new(zero),
            step: Box::new(step),
            bound: Box::new(bound),
            scrutinee: Box::new(scrutinee),
        }
    }
    pub fn fin0_elim(ty: Self, absurd: Self) -> Self {
        Self::Fin0Elim {
            ty: Box::new(ty),
            absurd: Box::new(absurd),
        }
    }

    pub fn eq(ty: Self, left: Self, right: Self) -> Self {
        Self::Eq {
            ty: Box::new(ty),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    pub fn refl(self) -> Self {
        Self::Refl(Box::new(self))
    }
    /// All J parameters are explicit; level is the motive's result universe.
    pub fn j(
        level: u32,
        ty: Self,
        left: Self,
        motive: Self,
        base: Self,
        right: Self,
        proof: Self,
    ) -> Self {
        Self::J {
            level,
            ty: Box::new(ty),
            left: Box::new(left),
            motive: Box::new(motive),
            base: Box::new(base),
            right: Box::new(right),
            proof: Box::new(proof),
        }
    }

    pub fn succ(self) -> Self {
        Self::Succ(Box::new(self))
    }
    pub fn nat_elim(level: u32, motive: Self, zero: Self, step: Self, scrutinee: Self) -> Self {
        Self::NatElim {
            level,
            motive: Box::new(motive),
            zero: Box::new(zero),
            step: Box::new(step),
            scrutinee: Box::new(scrutinee),
        }
    }

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
    Data {
        op: deppy_core::DataOp,
        arguments: Vec<T>,
    },
    Global(deppy_core::DefId),
    Inductive {
        id: deppy_core::InductiveId,
        parameters: Vec<T>,
    },
    Constructor {
        id: deppy_core::InductiveId,
        parameters: Vec<T>,
        fields: Vec<T>,
    },
    Elim {
        id: deppy_core::InductiveId,
        parameters: Vec<T>,
        level: u32,
        motive: T,
        branch: T,
        scrutinee: T,
    },

    Sigma {
        id: Id,
        domain: T,
        body: T,
    },
    Pair {
        ty: T,
        fst: T,
        snd: T,
    },
    Fst(T),
    Snd(T),
    Local(Id),
    Universe(u32),
    Eq {
        ty: T,
        left: T,
        right: T,
    },
    Refl {
        ty: T,
        value: T,
    },
    J {
        level: u32,
        ty: T,
        left: T,
        motive: T,
        base: T,
        right: T,
        proof: T,
    },
    Vec {
        ty: T,
        len: T,
    },
    VNil {
        ty: T,
    },
    VCons {
        ty: T,
        len: T,
        head: T,
        tail: T,
    },
    Fin {
        bound: T,
    },
    FZ {
        bound: T,
    },
    FS {
        bound: T,
        pred: T,
    },
    VecElim {
        level: u32,
        ty: T,
        motive: T,
        nil: T,
        cons: T,
        len: T,
        scrutinee: T,
    },
    FinElim {
        level: u32,
        motive: T,
        zero: T,
        step: T,
        bound: T,
        scrutinee: T,
    },
    Fin0Elim {
        ty: T,
        absurd: T,
    },
    Nat,
    Zero,
    Succ(T),
    NatElim {
        level: u32,
        motive: T,
        zero: T,
        step: T,
        scrutinee: T,
    },
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
