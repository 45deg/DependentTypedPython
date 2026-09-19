from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, Eq, refl
from deppy.equality import cong


@inductive
class Nat:
    @constructor
    def Z() -> Nat: ...
    @constructor
    def S(pred: Nat) -> Nat: ...


@dependent(decreases="n")
def add(n: Nat, m: Nat) -> Nat:
    match n:
        case Z():
            return m
        case S(k):
            return S(add(k, m))


@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, add(n, Z()), n]:
    match n:
        case Z():
            return refl(Z())
        case S(k):
            return cong(lambda value: S(value), zero_right(k))
