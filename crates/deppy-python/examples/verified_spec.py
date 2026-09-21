from __future__ import annotations
from deppy import theorem, Nat, Eq
from deppy.data import MkUnit
from deppy.nat import add
from deppy.nat_order import LE, LT
from deppy.verified import verified_spec
from verified import twice, advance
from verified_loop import countdown, accumulate


@theorem
def twice_spec(n: Nat) -> Eq[Nat, twice(n), add(n, n)]:
    r"""Reuse the verified specification :math:`\operatorname{twice}(n)=n+n`."""
    return verified_spec(twice, n, MkUnit())


@theorem
def advance_spec(n: Nat, limit: Nat, pre: LT(n, limit)) -> LE[advance(n, limit), limit]:
    r"""Reuse the update bound under its original strict precondition."""
    return verified_spec(advance, n, limit, pre)


@theorem
def countdown_spec(n: Nat) -> Eq[Nat, countdown(n), 0]:
    r"""Reuse the countdown result, including its checked termination argument."""
    return verified_spec(countdown, n, MkUnit())


@theorem
def accumulate_spec(n: Nat) -> Eq[Nat, accumulate(n), n]:
    r"""Reuse the accumulator's result for an arbitrary natural input."""
    return verified_spec(accumulate, n, MkUnit())
