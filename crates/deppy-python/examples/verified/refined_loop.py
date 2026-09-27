from deppy import theorem, Nat, Z, S, Eq, refl, absurd
from deppy.data import Bool, False_, MkUnit
from deppy.equality import sym
from deppy.tactics import exact
from deppy.nat import pred_or
from deppy.nat_order import LE, LT, le_refl, le_weaken, le_trans, lt_decide, pred_lt
from deppy.verified import verified, Refined, verified_spec, nat_lt, decision_true, false_ne_true
from deppy.verified_loop import invariant, decreases


@verified(proof=lambda n, positive: pred_lt(n, positive))
def decrement(n: Refined[Nat, lambda value: LT(0, value)]) -> Refined[Nat, lambda result: LT(result, n)]:
    r"""Return a strictly smaller natural number when :math:`0<n`."""
    return pred_or(0, n)


@theorem(decreases="n")
def stopped(n: Nat, test: Eq[Bool, nat_lt(0, n), False_()]) -> Eq[Nat, n, 0]:
    r"""The countdown guard is false only when :math:`n=0`."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@verified(proofs={
    "local.counter.refined": lambda n, pre, value: le_refl(n),
    "loop.init": lambda n, pre, initial, initial_bound: initial_bound,
    "loop.preserve.entry.local.counter.refined": lambda n, pre, initial, initial_bound, state, inv, test, old: exact(inv),
    "loop.preserve.call.counter.requires": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: decision_true(lt_decide(0, old), test),
    "loop.preserve.local.counter.refined": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, smaller: le_trans(le_weaken(smaller), n, inv),
    "loop.preserve": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, smaller, new_bound: exact(new_bound),
    "loop.decrease.entry.local.counter.refined": lambda n, pre, initial, initial_bound, state, inv, test, old: exact(inv),
    "loop.decrease.call.counter.requires": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: decision_true(lt_decide(0, old), test),
    "loop.decrease.local.counter.refined": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, smaller: le_trans(le_weaken(smaller), n, inv),
    "loop.decrease": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, smaller, new_bound: exact(smaller),
    "loop.exit.entry.local.counter.refined": lambda n, pre, initial, initial_bound, state, inv, test, old: exact(inv),
    "loop.exit": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: stopped(old, test),
})
def bounded_countdown(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 0]]:
    r"""Count down using only the helper contract, maintaining :math:`counter\le n`."""
    counter: Refined[Nat, lambda value: LE[value, n]] = n
    while 0 < counter:
        invariant(lambda counter: LE[counter, n], state=(counter,))
        decreases(lambda counter: counter)
        counter = decrement(counter)
    return counter
