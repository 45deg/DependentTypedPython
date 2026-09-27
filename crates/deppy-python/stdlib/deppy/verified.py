from __future__ import annotations
from deppy._builtins import Refined, verified, verified_spec, dependent, theorem, induct, Pi, Type, Nat, Z, S, Eq, refl, absurd
from deppy.data import Bool, False_, True_, Unit, MkUnit, Empty, Decidable, Yes, No
from deppy.equality import transport, sym
from deppy.nat import add, mul, pred_or
from deppy.bool import (
    and_left as _bool_and_left, and_right as _bool_and_right,
    bool_eq as _bool_bool_eq, bool_not as _bool_bool_not,
    decision_bool as _bool_decision_bool, decision_true as _bool_decision_true,
    decision_true_intro as _bool_decision_true_intro,
    false_ne_true as _bool_false_ne_true, false_true_elim as _bool_false_true_elim,
    false_type as _bool_false_type, not_false as _bool_not_false,
    select as _bool_select, select_post as _bool_select_post,
    select_post_eq as _bool_select_post_eq,
    true_false_elim as _bool_true_false_elim,
)
from deppy.nat_bool import (
    lt_le_bound as _nat_lt_le_bound, nat_eq as _nat_nat_eq,
    nat_eq_true as _nat_nat_eq_true, nat_le as _nat_nat_le,
    nat_le_refl_true as _nat_nat_le_refl_true,
    nat_le_true as _nat_nat_le_true, nat_lt as _nat_nat_lt,
    nat_lt_false_zero as _nat_nat_lt_false_zero,
    nat_lt_not_false as _nat_nat_lt_not_false,
    nat_lt_true as _nat_nat_lt_true, pred_lt_true as _nat_pred_lt_true,
)
from deppy.nat_order import pred_lt, LE, LT, le_decide, lt_decide, le_trans, le_weaken, le_antisymm, le_refl


@dependent
def decision_bool[P: Type](decision: Decidable[P]) -> Bool:
    r"""Compute a boolean from a constructive decision for :math:`P`."""
    return _bool_decision_bool[P](decision)


@dependent
def nat_le(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n \le m` for a verified branch condition."""
    return _nat_nat_le(n, m)


@dependent
def nat_lt(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n < m` for a verified branch condition."""
    return _nat_nat_lt(n, m)


@dependent
def select[A: Type](flag: Bool, no: A, yes: A) -> A:
    r"""Denote a branch: select ``yes`` when the flag is true, otherwise ``no``."""
    return _bool_select[A](flag, no, yes)


@theorem(decreases="flag")
def select_post[A: Type, P: Pi[A, lambda _: Type]](
    flag: Bool, no: A, yes: A, no_proof: P(no), yes_proof: P(yes)
) -> P(select[A](flag, no, yes)):
    r"""If :math:`P(x)` and :math:`P(y)`, then :math:`P(\operatorname{select}(b,x,y))`."""
    return _bool_select_post[A, P](flag, no, yes, no_proof, yes_proof)


@dependent(decreases="flag", motive_level=1)
def false_type(flag: Bool) -> Type:
    r"""A discriminating family: unit at false, empty at true."""
    return _bool_false_type(flag)


@theorem
def false_ne_true(proof: Eq[Bool, False_(), True_()]) -> Empty:
    r"""Boolean constructors are distinct: :math:`\mathrm{false} \ne \mathrm{true}`."""
    return _bool_false_ne_true(proof)


@theorem(decreases="decision")
def decision_true[P: Type](decision: Decidable[P], test: Eq[Bool, decision_bool(decision), True_()]) -> P:
    r"""Recover :math:`P` from a true constructive decision."""
    return _bool_decision_true[P](decision, test)


@theorem(decreases="flag")
def select_post_eq[A: Type, P: Pi[A, lambda _: Type]](
    flag: Bool, no: A, yes: A,
    no_proof: Pi[Eq[Bool, flag, False_()], lambda _: P(no)],
    yes_proof: Pi[Eq[Bool, flag, True_()], lambda _: P(yes)],
) -> P(select[A](flag, no, yes)):
    r"""Prove a selected result, assuming the corresponding boolean branch equation."""
    return _bool_select_post_eq[A, P](flag, no, yes, no_proof, yes_proof)


@theorem
def nat_lt_true(n: Nat, m: Nat, test: Eq[Bool, nat_lt(n, m), True_()]) -> LT(n, m):
    """Recover strict order evidence from a verified guard."""
    return _nat_nat_lt_true(n, m, test)


@theorem
def nat_le_true(n: Nat, m: Nat, test: Eq[Bool, nat_le(n, m), True_()]) -> LE[n, m]:
    """Recover non-strict order evidence from a verified guard."""
    return _nat_nat_le_true(n, m, test)


@theorem(decreases="n")
def nat_lt_false_zero(n: Nat, test: Eq[Bool, nat_lt(0, n), False_()]) -> Eq[Nat, n, 0]:
    """A natural number that is not positive is zero."""
    return _nat_nat_lt_false_zero(n, test)


@theorem
def lt_le_bound[n: Nat, m: Nat](smaller: LT(n, m), k: Nat, bound: LE[m, k]) -> LE[n, k]:
    """A strict decrease preserves an existing upper bound."""
    return _nat_lt_le_bound[n, m](smaller, k, bound)


@theorem
def pred_lt_true(n: Nat, test: Eq[Bool, nat_lt(0, n), True_()]) -> LT(pred_or(0, n), n):
    """A positive loop guard justifies decrementing the counter."""
    return _nat_pred_lt_true(n, test)


@dependent
def bool_not(flag: Bool) -> Bool:
    """Negate a Bool without Python truthiness."""
    return _bool_bool_not(flag)


@dependent
def bool_eq(left: Bool, right: Bool) -> Bool:
    """Compare Boolean values."""
    return _bool_bool_eq(left, right)


@dependent
def nat_eq(left: Nat, right: Nat) -> Bool:
    """Compare natural numbers using checked order decisions."""
    return _nat_nat_eq(left, right)


@theorem
def false_true_elim[P: Type](proof: Eq[Bool, False_(), True_()]) -> P:
    """Eliminate an impossible false-equals-true branch."""
    return _bool_false_true_elim[P](proof)


@theorem
def true_false_elim[P: Type](proof: Eq[Bool, True_(), False_()]) -> P:
    """Eliminate an impossible true-equals-false branch."""
    return _bool_true_false_elim[P](proof)


@theorem(decreases="flag")
def not_false(flag: Bool, proof: Eq[Bool, bool_not(flag), False_()]) -> Eq[Bool, flag, True_()]:
    """Recover a true flag from a false negation."""
    return _bool_not_false(flag, proof)


@theorem
def nat_lt_not_false(n: Nat, m: Nat, proof: Eq[Bool, bool_not(nat_lt(n, m)), False_()]) -> LT(n, m):
    """Recover strict order on the false branch of a negated guard."""
    return _nat_nat_lt_not_false(n, m, proof)


@theorem(decreases="left")
def and_left(left: Bool, right: Bool, proof: Eq[Bool, select[Bool](left, False_(), right), True_()]) -> Eq[Bool, left, True_()]:
    """Recover the left conjunct of a true Boolean conjunction."""
    return _bool_and_left(left, right, proof)


@theorem(decreases="left")
def and_right(left: Bool, right: Bool, proof: Eq[Bool, select[Bool](left, False_(), right), True_()]) -> Eq[Bool, right, True_()]:
    """Recover the right conjunct of a true Boolean conjunction."""
    return _bool_and_right(left, right, proof)


@theorem
def nat_eq_true(n: Nat, m: Nat, proof: Eq[Bool, nat_eq(n, m), True_()]) -> Eq[Nat, n, m]:
    """Recover propositional equality from a true equality guard."""
    return _nat_nat_eq_true(n, m, proof)


@theorem(decreases="decision")
def decision_true_intro[P: Type](decision: Decidable[P], proof: P) -> Eq[Bool, decision_bool(decision), True_()]:
    """A witness makes its constructive decision true."""
    return _bool_decision_true_intro[P](decision, proof)


@theorem
def nat_le_refl_true(n: Nat) -> Eq[Bool, nat_le(n, n), True_()]:
    """The non-strict comparison of a natural number with itself is true."""
    return _nat_nat_le_refl_true(n)
