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
    T::Vec { ty: a, len }.arc()
}
pub fn nil(a: Tm) -> Tm {
    T::VNil { ty: a }.arc()
}
pub fn cons(a: Tm, len: Tm, head: Tm, tail: Tm) -> Tm {
    T::VCons {
        ty: a,
        len,
        head,
        tail,
    }
    .arc()
}
pub fn fin(bound: Tm) -> Tm {
    T::Fin { bound }.arc()
}
pub fn fz(bound: Tm) -> Tm {
    T::FZ { bound }.arc()
}
pub fn fs(bound: Tm, pred: Tm) -> Tm {
    T::FS { bound, pred }.arc()
}
