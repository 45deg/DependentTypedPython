from __future__ import annotations
from deppy import theorem, Nat, S, Eq, refl
from deppy.verified import verified, Refined, verified_spec
from deppy.tactics import exact, rewrite


@verified(proof=lambda n, pre: rewrite(pre, refl(1)))
def zero_to_one(n: Refined[Nat, lambda value: Eq[Nat, value, 0]]) -> Refined[Nat, lambda result: Eq[Nat, result, 1]]:
    r"""Require :math:`n=0` and establish :math:`result=1` by rewriting."""
    return S(n)


@verified(proof=lambda n, pre: rewrite(pre, refl(2)))
def one_to_two(n: Refined[Nat, lambda value: Eq[Nat, value, 1]]) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    r"""Require :math:`n=1` and establish :math:`result=2` by rewriting."""
    return S(n)


@verified(proofs={
    "call.first.requires": lambda n, pre: exact(pre),
    "call.second.requires": lambda n, pre, first, first_spec: exact(first_spec),
    "return": lambda n, pre, first, first_spec, second, second_spec: exact(second_spec),
})
def composed(n: Refined[Nat, lambda value: Eq[Nat, value, 0]]) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    r"""Compose refined arguments using :math:`n=0`, then :math:`first=1`."""
    first = zero_to_one(n)
    second = one_to_two(first)
    return second


@theorem
def composed_correct() -> Eq[Nat, composed(0), 2]:
    r"""Reuse the composed specification with the refinement evidence :math:`0=0`."""
    return verified_spec(composed, 0, refl(0))
