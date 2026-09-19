//! Fully explicit dependent core. No Python execution or metavariables; axioms are explicit opaque declarations.
//! Type-directed erasure runs after independent kernel validation.
mod data;
pub use data::{ConstructorDecl, DataDecl, DataOp};
mod inductive;
mod kernel;
pub use inductive::{InductiveDecl, InductiveId};
mod value;

pub use kernel::{Error, Kernel, RuntimeSignature, RuntimeTerm, RuntimeType};
use std::sync::Arc;

pub type Tm = Arc<Term>;
pub type DefId = u64;
/// A closed, transparent definition with concrete universe levels.
#[derive(Clone, Debug)]
pub struct Definition {
    pub ty: Tm,
    pub body: Tm,
}

/// A checked global declaration. A missing body is an explicitly declared axiom.
/// Opaque definitions retain checked bodies for dependency tracking and extraction.
/// The environment never mutates an axiom into a definition.
#[derive(Clone, Debug)]
pub struct GlobalDeclaration {
    pub ty: Tm,
    pub body: Option<Tm>,
    pub transparency: Transparency,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Transparency {
    Transparent,
    Opaque,
}

impl GlobalDeclaration {
    /// Only transparent definitions participate in conversion.
    pub fn unfolding_body(&self) -> Option<&Tm> {
        match self.transparency {
            Transparency::Transparent => self.body.as_ref(),
            Transparency::Opaque => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relevance {
    Erased,
    Runtime,
}

/// Variables use de Bruijn indices: zero denotes the nearest binder.
/// Universe levels are concrete and non-cumulative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Data {
        op: DataOp,
        arguments: Vec<Tm>,
    },
    Global(DefId),
    Inductive {
        id: InductiveId,
        parameters: Vec<Tm>,
    },
    Constructor {
        id: InductiveId,
        parameters: Vec<Tm>,
        fields: Vec<Tm>,
    },
    Elim {
        id: InductiveId,
        parameters: Vec<Tm>,
        level: u32,
        motive: Tm,
        branch: Tm,
        scrutinee: Tm,
    },

    Sigma {
        domain: Tm,
        codomain: Tm,
    },
    Pair {
        ty: Tm,
        fst: Tm,
        snd: Tm,
    },
    Fst(Tm),
    Snd(Tm),
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
    Vec {
        ty: Tm,
        len: Tm,
    },
    VNil {
        ty: Tm,
    },
    VCons {
        ty: Tm,
        len: Tm,
        head: Tm,
        tail: Tm,
    },
    Fin {
        bound: Tm,
    },
    FZ {
        bound: Tm,
    },
    FS {
        bound: Tm,
        pred: Tm,
    },
    /// P : (n : Nat) -> Vec A n -> Type[level].
    /// cons : (k : Nat) -> (h : A) -> (t : Vec A k) -> P k t -> P (S k) (VCons A k h t).
    VecElim {
        level: u32,
        ty: Tm,
        motive: Tm,
        nil: Tm,
        cons: Tm,
        len: Tm,
        scrutinee: Tm,
    },
    /// P : (n : Nat) -> Fin n -> Type[level], with FZ and FS branches.
    FinElim {
        level: u32,
        motive: Tm,
        zero: Tm,
        step: Tm,
        bound: Tm,
        scrutinee: Tm,
    },
    /// Eliminate an impossible Fin Z into the explicitly supplied type.
    Fin0Elim {
        ty: Tm,
        absurd: Tm,
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
