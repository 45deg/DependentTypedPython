from __future__ import annotations
from deppy import dependent, Type, Nat, S, Eq, refl, absurd
from deppy.nat import add, pred_or
from deppy.data import Empty, decision_weight
from deppy.nat_order import LE, LT, LEZero, LESucc, le_decide, lt_decide, le_refl, le_step, le_antisymm, lt_irrefl, lt_trans, add_le_add_left, add_le_add_right, add_lt_add_right, pred_lt

@dependent
def empty_target[A: Type](n: Nat, p: LE[S(n), 0]) -> A:
    return absurd(A, p)

@dependent
def higher_target(n: Nat, p: LE[S(n), 0]) -> Type:
    return absurd(Type, p)
