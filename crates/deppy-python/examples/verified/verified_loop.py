from __future__ import annotations
from deppy import theorem, Nat, Z, S, Eq, refl, absurd, Pair
from deppy.data import Bool, False_, True_, Unit, MkUnit
from deppy.equality import sym, trans, transport
from deppy.nat import pred_or, add, add_zero, add_succ
from deppy.nat_order import lt_decide, pred_lt
from deppy.verified import verified, nat_lt, decision_true, false_ne_true
from deppy.verified_loop import invariant, decreases


@theorem(decreases="n")
def stopped_at_zero(n: Nat, test: Eq[Bool, nat_lt(0, n), False_()]) -> Eq[Nat, n, 0]:
    r"""A natural countdown stops only at zero: :math:`\neg(0<n) \Rightarrow n=0`."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@verified(
    ensures=lambda n, result: Eq[Nat, result, 0],
    proof=lambda n, pre: Pair(
        MkUnit(),
        Pair(lambda state, inv, test: MkUnit(),
        Pair(lambda state, inv, test: pred_lt(state.fst, decision_true(lt_decide(0, state.fst), test)),
        lambda state, inv, test: stopped_at_zero(state.fst, test))),
    ),
)
def countdown(n: Nat) -> Nat:
    r"""Decrement a natural counter to zero, with a checked termination proof."""
    counter = n
    while 0 < counter:
        invariant(lambda counter: Unit, state=(counter,))
        decreases(lambda counter: counter)
        counter = pred_or(0, counter)
    return counter


@theorem(decreases="counter")
def add_loop_preserve(n: Nat, counter: Nat, total: Nat, inv: Eq[Nat, add(counter, total), n], test: Eq[Bool, nat_lt(0, counter), True_()]) -> Eq[Nat, add(pred_or(0, counter), S(total)), n]:
    r"""Moving one unit from the counter to the accumulator preserves their sum."""
    match counter:
        case Z():
            return absurd(Eq[Nat, add(pred_or(0, 0), S(total)), n], false_ne_true(test))
        case S(k):
            return trans(add_succ(k, total), inv)


@theorem
def add_loop_exit(n: Nat, counter: Nat, total: Nat, inv: Eq[Nat, add(counter, total), n], test: Eq[Bool, nat_lt(0, counter), False_()]) -> Eq[Nat, total, n]:
    r"""At exit the counter is zero, so the accumulator equals the initial sum."""
    return transport[Nat, counter, 0](lambda k: Eq[Nat, add(k, total), n], stopped_at_zero(counter, test), inv)


@verified(
    ensures=lambda n, result: Eq[Nat, result, n],
    proof=lambda n, pre: Pair(
        add_zero(n),
        Pair(lambda state, inv, test: add_loop_preserve(n, state.fst, state.snd.fst, inv, test),
        Pair(lambda state, inv, test: pred_lt(state.fst, decision_true(lt_decide(0, state.fst), test)),
        lambda state, inv, test: add_loop_exit(n, state.fst, state.snd.fst, inv, test))),
    ),
)
def accumulate(n: Nat) -> Nat:
    r"""Transfer :math:`n` units to an accumulator, proving result and termination."""
    counter = n
    total = 0
    while 0 < counter:
        invariant(lambda counter, total: Eq[Nat, add(counter, total), n], state=(counter, total))
        decreases(lambda counter, total: counter)
        total = S(total)
        counter = pred_or(0, counter)
    return total
