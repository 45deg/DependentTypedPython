from __future__ import annotations
from deppy import dependent, Type, Nat, S, Eq, refl, absurd
from deppy.nat import add, pred_or
from deppy.data import Empty, decision_weight
from deppy.nat_order import LE, LT, LEZero, LESucc, le_decide, lt_decide, le_refl, le_step, le_antisymm, lt_irrefl, lt_trans, add_le_add_left, add_le_add_right, add_lt_add_right, pred_lt

@dependent
def bounds(n: Nat, m: Nat, p: LE[n, m], q: LE[m, n]) -> Eq[Nat, n, m]:
    return le_antisymm(p, q)

@dependent
def prefix(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[add(k, n), add(k, m)]:
    return add_le_add_left(n, m, k, p)

@dependent
def suffix(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[add(n, k), add(m, k)]:
    return add_le_add_right(p, k)

@dependent
def strict_suffix(n: Nat, m: Nat, k: Nat, p: LT(n, m)) -> LT(add(n, k), add(m, k)):
    return add_lt_add_right(n, m, k, p)

@dependent
def descent(n: Nat, p: LT(0, n)) -> LT(pred_or(0, n), n):
    return pred_lt(n, p)

@dependent
def no_cycle(n: Nat, m: Nat, p: LT(n, m), q: LT(m, n)) -> Empty:
    return lt_irrefl(n, lt_trans(n, m, n, p, q))

@dependent
def one_step(n: Nat) -> LT(pred_or(0, S(n)), S(n)):
    return pred_lt(S(n), LESucc(0, n, LEZero(n)))
