from __future__ import annotations
from deppy._builtins import dependent, theorem, Type, Nat, S, Fin, FZ, FS, Pi, Eq, refl, absurd, fin0_elim, nat_elim, fin_elim
from deppy.nat_order import LT, LEZero, LESucc
from deppy.nat import succ_injective, zero_ne_succ
from deppy.equality import sym, cong


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
    """Eliminate a finite index by its zero or successor case."""
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


@theorem(decreases="i")
def to_nat_injective(n: Nat, i: Fin[n], j: Fin[n], equal: Eq[Nat, to_nat(n, i), to_nat(n, j)]) -> Eq[Fin[n], i, j]:
    """Finite indices with the same natural-number value are equal."""
    match i:
        case FZ(k):
            return fin_case(k, lambda q: Pi[
                Eq[Nat, 0, to_nat(S(k), q)], lambda _: Eq[Fin[S(k)], FZ(k), q]
            ], j,
                lambda same: refl(FZ(k)),
                lambda other: lambda same: absurd(
                    Eq[Fin[S(k)], FZ(k), FS(k, other)], zero_ne_succ(to_nat(k, other), same)
                ),
            )(equal)
        case FS(k, inner):
            return fin_case(k, lambda q: Pi[
                Eq[Nat, S(to_nat(k, inner)), to_nat(S(k), q)],
                lambda _: Eq[Fin[S(k)], FS(k, inner), q]
            ], j,
                lambda same: absurd(
                    Eq[Fin[S(k)], FS(k, inner), FZ(k)], zero_ne_succ(to_nat(k, inner), sym(same))
                ),
                lambda other: lambda same: cong(
                    lambda q: FS(k, q),
                    to_nat_injective(k, inner, other,
                        succ_injective(to_nat(k, inner), to_nat(k, other), same)),
                ),
            )(equal)
