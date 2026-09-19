from __future__ import annotations
from deppy._builtins import dependent, Type, Pi, Eq, refl, J


@dependent
def sym[A: Type, x: A, y: A](p: Eq[A, x, y]) -> Eq[A, y, x]:
    return J(0, A, x, lambda end, proof: Eq[A, end, x], refl(x), y, p)


@dependent
def trans[A: Type, x: A, y: A, z: A](p: Eq[A, x, y], q: Eq[A, y, z]) -> Eq[A, x, z]:
    return J(0, A, y, lambda end, proof: Eq[A, x, end], p, z, q)


@dependent
def cong[A: Type, B: Type, x: A, y: A](f: Pi[A, lambda arg: B], p: Eq[A, x, y]) -> Eq[B, f(x), f(y)]:
    return J(0, A, x, lambda end, proof: Eq[B, f(x), f(end)], refl(f(x)), y, p)


@dependent
def transport[A: Type, x: A, y: A](P: Pi[A, lambda arg: Type], p: Eq[A, x, y], value: P(x)) -> P(y):
    return J(0, A, x, lambda end, proof: P(end), value, y, p)
