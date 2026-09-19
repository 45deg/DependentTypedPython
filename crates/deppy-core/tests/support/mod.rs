#![allow(dead_code)]
use deppy_core::{Relevance::Runtime, Term as T, Tm};
pub fn n() -> Tm {
    T::Nat.arc()
}
pub fn z() -> Tm {
    T::Zero.arc()
}
pub fn s(x: Tm) -> Tm {
    T::Succ(x).arc()
}
pub fn v(i: usize) -> Tm {
    T::Var(i).arc()
}
pub fn u(i: u32) -> Tm {
    T::Universe(i).arc()
}
pub fn lam(a: Tm, b: Tm) -> Tm {
    T::Lam {
        relevance: Runtime,
        domain: a,
        body: b,
    }
    .arc()
}
pub fn pi(a: Tm, b: Tm) -> Tm {
    T::Pi {
        relevance: Runtime,
        domain: a,
        codomain: b,
    }
    .arc()
}
pub fn app(f: Tm, x: Tm) -> Tm {
    T::App {
        function: f,
        argument: x,
    }
    .arc()
}
pub fn vec(a: Tm, len: Tm) -> Tm {
    T::Vec(a, len).arc()
}
pub fn nil(a: Tm) -> Tm {
    T::VNil(a).arc()
}
pub fn cons(a: Tm, len: Tm, head: Tm, tail: Tm) -> Tm {
    T::VCons(a, len, head, tail).arc()
}
pub fn fin(bound: Tm) -> Tm {
    T::Fin(bound).arc()
}
pub fn fz(bound: Tm) -> Tm {
    T::FZ(bound).arc()
}
pub fn fs(bound: Tm, pred: Tm) -> Tm {
    T::FS(bound, pred).arc()
}
pub fn ve(level: u32, ty: Tm, motive: Tm, nil: Tm, cons: Tm, len: Tm, scrutinee: Tm) -> Tm {
    T::VecElim(level, ty, motive, nil, cons, len, scrutinee).arc()
}
pub fn fe(level: u32, motive: Tm, zero: Tm, step: Tm, bound: Tm, scrutinee: Tm) -> Tm {
    T::FinElim(level, motive, zero, step, bound, scrutinee).arc()
}
pub fn eq(ty: Tm, left: Tm, right: Tm) -> Tm {
    T::Eq { ty, left, right }.arc()
}
pub fn refl(ty: Tm, value: Tm) -> Tm {
    T::Refl { ty, value }.arc()
}
pub fn absurd(ty: Tm, value: Tm) -> Tm {
    T::Fin0Elim(ty, value).arc()
}
