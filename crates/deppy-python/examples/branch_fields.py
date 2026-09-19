from __future__ import annotations
from deppy import dependent, record, Nat, Z, S


@record
class Count:
    value: Nat


@record
class WrappedCount:
    value: Count


@dependent(decreases="n")
def count(n: Nat) -> Nat:
    match n:
        case Z():
            box = Count(Z())
            return box.value
        case S(k):
            previous: Nat = count(k)
            box = WrappedCount(Count(S(previous)))
            return box.value.value
