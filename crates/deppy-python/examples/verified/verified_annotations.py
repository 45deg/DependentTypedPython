from __future__ import annotations
from deppy import Nat, Eq
from deppy.nat import pred_or
from deppy.nat_order import LE, LT
from deppy.verified import verified, Refined
from deppy.verified_loop import decreases


@verified
def decrement(n: Refined[Nat, lambda value: LT(0, value)]) -> Refined[Nat, lambda result: LT(result, n)]:
    return pred_or(0, n)


@verified
def bounded_countdown(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 0]]:
    counter: Refined[Nat, lambda value: LE[value, n]] = n
    while 0 < counter:
        decreases(counter)
        counter = decrement(counter)
    return counter
