from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, Eq, refl
from deppy.equality import cong


@inductive
class Nat:
    """Demonstration natural numbers, distinct from the canonical builtin Nat."""
    @constructor
    def Z() -> Nat: ...
    @constructor
    def S(pred: Nat) -> Nat: ...


@dependent(decreases="n")
def add(n: Nat, m: Nat) -> Nat:
    """Add demonstration natural numbers."""
    match n:
        case Z():
            return m
        case S(k):
            return S(add(k, m))


@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, add(n, Z()), n]:
    """Adding demonstration zero on the right preserves the number."""
    match n:
        case Z():
            return refl(Z())
        case S(k):
            return cong(lambda value: S(value), zero_right(k))
