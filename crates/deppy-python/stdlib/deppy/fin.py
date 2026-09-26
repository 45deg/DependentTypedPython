from __future__ import annotations
from deppy._builtins import dependent, theorem, Type, Nat, S, Fin, FZ, FS, Pi, nat_elim, fin_elim
from deppy.nat_order import LT, LEZero, LESucc


@dependent
def case_motive(size: Nat) -> Pi[Fin[size], lambda index: Type[1]]:
    return nat_elim(
        2,
        lambda size: Pi[Fin[size], lambda index: Type[1]],
        lambda index: Type,
        lambda k, unused: lambda index: Pi[
            Pi[Fin[S(k)], lambda j: Type],
            lambda P: Pi[P(FZ(k)), lambda first: Pi[
                Pi[Fin[k], lambda j: P(FS(k, j))],
                lambda rest: P(index),
            ]],
        ],
        size,
    )


@dependent
def fin_case(k: Nat, P: Pi[Fin[S(k)], lambda index: Type], i: Fin[S(k)],
             first: P(FZ(k)), rest: Pi[Fin[k], lambda j: P(FS(k, j))]) -> P(i):
    return fin_elim(
        1,
        lambda size, index: case_motive(size)(index),
        lambda k, family, zero, step: zero,
        lambda k, j, unused, family, zero, step: step(j),
        S(k), i,
    )(P)(first)(rest)


@dependent(decreases="i")
def to_nat(n: Nat, i: Fin[n]) -> Nat:
    """Return the zero-based natural-number value of a finite index."""
    match i:
        case FZ(_):
            return 0
        case FS(k, j):
            return S(to_nat(k, j))


@theorem(decreases="i")
def to_nat_lt(n: Nat, i: Fin[n]) -> LT(to_nat(n, i), n):
    """Every finite index lies strictly below its size."""
    match i:
        case FZ(k):
            return LESucc(0, k, LEZero(k))
        case FS(k, j):
            return LESucc(S(to_nat(k, j)), k, to_nat_lt(k, j))
