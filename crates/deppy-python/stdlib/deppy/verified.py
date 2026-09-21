from __future__ import annotations
from deppy._builtins import Refined, verified, verified_spec, dependent, theorem, induct, Pi, Type, Nat, Z, S, Eq, refl, absurd
from deppy.data import Bool, False_, True_, Unit, MkUnit, Empty, Decidable, Yes, No
from deppy.equality import transport, sym
from deppy.nat import add, mul, pred_or
from deppy.nat_order import pred_lt, LE, LT, le_decide, lt_decide, le_trans, le_weaken


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


@theorem(decreases="flag")
def select_post_eq[A: Type, P: Pi[A, lambda _: Type]](
    flag: Bool, no: A, yes: A,
    no_proof: Pi[Eq[Bool, flag, False_()], lambda _: P(no)],
    yes_proof: Pi[Eq[Bool, flag, True_()], lambda _: P(yes)],
) -> P(select[A](flag, no, yes)):
    r"""Prove a selected result, assuming the corresponding boolean branch equation."""
    match flag:
        case False_():
            return no_proof(refl(False_()))
        case True_():
            return yes_proof(refl(True_()))


@theorem
def nat_lt_true(n: Nat, m: Nat, test: Eq[Bool, nat_lt(n, m), True_()]) -> LT(n, m):
    """Recover strict order evidence from a verified guard."""
    return decision_true(lt_decide(n, m), test)


@theorem
def nat_le_true(n: Nat, m: Nat, test: Eq[Bool, nat_le(n, m), True_()]) -> LE[n, m]:
    """Recover non-strict order evidence from a verified guard."""
    return decision_true(le_decide(n, m), test)


@theorem(decreases="n")
def nat_lt_false_zero(n: Nat, test: Eq[Bool, nat_lt(0, n), False_()]) -> Eq[Nat, n, 0]:
    """A natural number that is not positive is zero."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@theorem
def lt_le_bound[n: Nat, m: Nat](smaller: LT(n, m), k: Nat, bound: LE[m, k]) -> LE[n, k]:
    """A strict decrease preserves an existing upper bound."""
    return le_trans(le_weaken(smaller), k, bound)


@theorem
def pred_lt_true(n: Nat, test: Eq[Bool, nat_lt(0, n), True_()]) -> LT(pred_or(0, n), n):
    """A positive loop guard justifies decrementing the counter."""
    return pred_lt(n, nat_lt_true(0, n, test))
