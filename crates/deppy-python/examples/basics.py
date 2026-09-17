from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Eq, refl, Vec, VNil, Sigma, Pair


@dependent
def identity[A: Type](x: A) -> A:
    return x


@dependent
def twice(n: Nat) -> Nat:
    first: Nat = S(n)
    second = S(first)
    return identity(second)


@dependent
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    proof = refl(n)
    return proof


@dependent
def empty(n: Nat) -> Vec[Nat, Z()]:
    return VNil()


@dependent
def pack[T: Type](n: Nat, xs: Vec[T, n]) -> Sigma[Nat, lambda k: Vec[T, k]]:
    return Pair(n, xs)


assert identity(Z()) == Z()
