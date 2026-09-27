from __future__ import annotations
from deppy import dependent, Nat, Eq
from deppy.data import Empty
from deppy.nat_order import LE, LT, le_antisymm, lt_irrefl, lt_trans


# Part 5: order propositions are types whose values are proofs.
# LE[n, m] means n ≤ m; LT(n, m) means n < m; Empty has no values.


@dependent
def same_if_both_ways(n: Nat, m: Nat, forward: LE[n, m], backward: LE[m, n]) -> Eq[Nat, n, m]:
    # Antisymmetry: n ≤ m ∧ m ≤ n → n = m.
    # Both inequalities are proof arguments; no numeric search is needed here.
    return le_antisymm(forward, backward)


@dependent
def no_strict_cycle(n: Nat, m: Nat, forward: LT(n, m), backward: LT(m, n)) -> Empty:
    # n < m ∧ m < n → n < n, contradicting irreflexivity.
    # Returning Empty proves these two assumptions cannot hold together.
    return lt_irrefl(n, lt_trans(n, m, n, forward, backward))
