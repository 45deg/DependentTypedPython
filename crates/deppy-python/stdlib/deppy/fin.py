from __future__ import annotations
from deppy import dependent, Type, Nat, S, Fin, FZ, FS, Pi, nat_elim, fin_elim


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
