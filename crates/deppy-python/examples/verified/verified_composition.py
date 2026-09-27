from deppy import theorem, Nat, S, Eq, refl
from deppy.equality import cong
from deppy.verified import verified, Refined, verified_spec


@verified(
    requires=lambda n: Eq[Nat, n, 0],
    proof=lambda n, pre: cong[Nat, Nat](lambda x: S(x), pre),
)
def zero_to_one(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 1]]:
    r"""Under :math:`n=0`, return a value equal to :math:`1`."""
    return S(n)


@verified(
    requires=lambda n: Eq[Nat, n, 1],
    proof=lambda n, pre: cong[Nat, Nat](lambda x: S(x), pre),
)
def one_to_two(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    r"""Under :math:`n=1`, return a value equal to :math:`2`."""
    return S(n)


@verified(
    requires=lambda n: Eq[Nat, n, 0],
    proofs={
        "call.first.requires": lambda n, pre: pre,
        "call.second.requires": lambda n, pre, first, first_spec: first_spec,
        "return": lambda n, pre, first, first_spec, second, second_spec: second_spec,
    },
)
def composed(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    r"""Compose two contracts, proving :math:`n=0 \Rightarrow result=2`."""
    first = zero_to_one(n)
    second = one_to_two(first)
    return second


@theorem
def composed_correct() -> Eq[Nat, composed(0), 2]:
    r"""Reuse the composed function's kernel-checked contract."""
    return verified_spec(composed, 0, refl(0))
