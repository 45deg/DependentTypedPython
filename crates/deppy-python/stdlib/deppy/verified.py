from __future__ import annotations
from deppy._builtins import verified, dependent, theorem, induct, Pi, Type, Nat, Eq, absurd
from deppy.data import Bool, False_, True_, Unit, MkUnit, Empty, Decidable, Yes, No
from deppy.equality import transport
from deppy.nat import add, mul
from deppy.nat_order import le_decide, lt_decide


@dependent
def decision_bool[P: Type](decision: Decidable[P]) -> Bool:
    r"""Compute a boolean from a constructive decision for :math:`P`."""
    match decision:
        case Yes(_):
            return True_()
        case No(_):
            return False_()


@dependent
def nat_le(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n \le m` for a verified branch condition."""
    return decision_bool(le_decide(n, m))


@dependent
def nat_lt(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n < m` for a verified branch condition."""
    return decision_bool(lt_decide(n, m))


@dependent
def select[A: Type](flag: Bool, no: A, yes: A) -> A:
    r"""Denote a branch: select ``yes`` when the flag is true, otherwise ``no``."""
    return induct(0, flag, lambda _: A, no, yes)


@theorem(decreases="flag")
def select_post[A: Type, P: Pi[A, lambda _: Type]](
    flag: Bool, no: A, yes: A, no_proof: P(no), yes_proof: P(yes)
) -> P(select[A](flag, no, yes)):
    r"""If :math:`P(x)` and :math:`P(y)`, then :math:`P(\operatorname{select}(b,x,y))`."""
    match flag:
        case False_():
            return no_proof
        case True_():
            return yes_proof


@dependent(decreases="flag", motive_level=1)
def false_type(flag: Bool) -> Type:
    r"""A discriminating family: unit at false, empty at true."""
    match flag:
        case False_():
            return Unit
        case True_():
            return Empty


@theorem
def false_ne_true(proof: Eq[Bool, False_(), True_()]) -> Empty:
    r"""Boolean constructors are distinct: :math:`\mathrm{false} \ne \mathrm{true}`."""
    return transport[Bool, False_(), True_()](false_type, proof, MkUnit())


@theorem(decreases="decision")
def decision_true[P: Type](decision: Decidable[P], test: Eq[Bool, decision_bool(decision), True_()]) -> P:
    r"""Recover :math:`P` from a true constructive decision."""
    match decision:
        case Yes(proof):
            return proof
        case No(_):
            return absurd(P, false_ne_true(test))
