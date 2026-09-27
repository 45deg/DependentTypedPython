from __future__ import annotations
from deppy import dependent, Nat, Eq, refl, J, sym


@dependent
def erased[p: Eq[Nat, 0, 0]]() -> Eq[Nat, 0, 0]:
    return sym(p)


@dependent
def proof(n: Nat) -> Eq[Nat, n, n]:
    return sym(refl(n))


@dependent
def keep[p: Eq[Nat, 0, 0]](n: Nat) -> Nat:
    unused_proof = p
    return n


@dependent
def compute(n: Nat) -> Nat:
    return J(0, Nat, n, lambda end, p: Nat, n, n, proof(n))
