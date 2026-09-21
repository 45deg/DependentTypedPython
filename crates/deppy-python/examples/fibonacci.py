from __future__ import annotations
from deppy import dependent, theorem, Nat, Z, S, Type, Sigma, Eq, refl, Pair, absurd
from deppy.data import Bool, False_, True_, MkUnit
from deppy.equality import cong, cong2, trans, sym, transport
from deppy.nat import add, add_zero, add_succ, pred_or
from deppy.nat_order import lt_decide, pred_lt
from deppy.verified import verified, Refined, verified_spec, nat_lt, decision_true, false_ne_true
from deppy.verified_loop import invariant, decreases


@dependent(decreases="n")
def fib_pair(n: Nat) -> Sigma[Nat, lambda _: Nat]:
    r"""Recursively compute the consecutive values :math:`(F_n,F_{n+1})`."""
    match n:
        case Z():
            return Pair(0, 1)
        case S(k):
            previous = fib_pair(k)
            return Pair(previous.snd, add(previous.fst, previous.snd))


@dependent
def fib_recursive(n: Nat) -> Nat:
    r"""The recursive specification :math:`F_0=0`, :math:`F_1=1`, :math:`F_{n+2}=F_n+F_{n+1}`."""
    return fib_pair(n).fst


@theorem
def fib_step(n: Nat) -> Eq[Nat, add(fib_recursive(n), fib_recursive(S(n))), fib_recursive(S(S(n)))]:
    r"""The Fibonacci recurrence :math:`F_n+F_{n+1}=F_{n+2}`."""
    return refl(add(fib_recursive(n), fib_recursive(S(n))))


@dependent
def FibInvariant(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat) -> Type:
    r"""The loop invariant :math:`r+i=n \land a=F_i \land b=F_{i+1}`."""
    return Sigma[Eq[Nat, add(remaining, index), n], lambda count:
        Sigma[Eq[Nat, a, fib_recursive(index)], lambda current:
        Eq[Nat, b, fib_recursive(S(index))]]]


@theorem(decreases="remaining")
def counter_step(n: Nat, remaining: Nat, index: Nat, count: Eq[Nat, add(remaining, index), n], test: Eq[Bool, nat_lt(0, remaining), True_()]) -> Eq[Nat, add(pred_or(0, remaining), S(index)), n]:
    r"""Decrementing the remaining count and incrementing the index preserves :math:`r+i=n`."""
    match remaining:
        case Z():
            return absurd(Eq[Nat, add(pred_or(0, 0), S(index)), n], false_ne_true(test))
        case S(k):
            return trans(add_succ(k, index), count)


@theorem
def fib_preserve(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat, inv: FibInvariant(n, remaining, index, a, b), test: Eq[Bool, nat_lt(0, remaining), True_()]) -> FibInvariant(n, pred_or(0, remaining), S(index), b, add(a, b)):
    r"""One simultaneous Fibonacci update preserves all three invariant clauses."""
    return Pair(counter_step(n, remaining, index, inv.fst, test),
        Pair(inv.snd.snd,
            trans(cong2[Nat, Nat, Nat](lambda x: lambda y: add(x, y), inv.snd.fst, inv.snd.snd), fib_step(index))))


@theorem(decreases="remaining")
def counter_zero(remaining: Nat, test: Eq[Bool, nat_lt(0, remaining), False_()]) -> Eq[Nat, remaining, 0]:
    r"""A false positive-counter guard implies :math:`r=0`."""
    match remaining:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@theorem
def fib_exit(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat, inv: FibInvariant(n, remaining, index, a, b), test: Eq[Bool, nat_lt(0, remaining), False_()]) -> Eq[Nat, a, fib_recursive(n)]:
    r"""At exit :math:`r=0`, hence :math:`i=n` and :math:`a=F_n`."""
    index_is_n = transport[Nat, remaining, 0](lambda r: Eq[Nat, add(r, index), n], counter_zero(remaining, test), inv.fst)
    return trans(inv.snd.fst, cong[Nat, Nat](fib_recursive, index_is_n))


@verified(
    proofs={
        "loop.init": lambda n, pre: Pair(add_zero(n), Pair(refl(0), refl(1))),
        "loop.preserve": lambda n, pre, state, inv, test: fib_preserve(n, state.fst, state.snd.fst, state.snd.snd.fst, state.snd.snd.snd.fst, inv, test),
        "loop.decrease": lambda n, pre, state, inv, test: pred_lt(state.fst, decision_true(lt_decide(0, state.fst), test)),
        "loop.exit": lambda n, pre, state, inv, test: fib_exit(n, state.fst, state.snd.fst, state.snd.snd.fst, state.snd.snd.snd.fst, inv, test),
    },
)
def fib_loop(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, fib_recursive(n)]]:
    r"""Compute Fibonacci by a loop, proving :math:`\operatorname{fib\_loop}(n)=F_n` and termination."""
    remaining = n
    index = 0
    a, b = 0, 1
    while 0 < remaining:
        invariant(lambda remaining, index, a, b: FibInvariant(n, remaining, index, a, b), state=(remaining, index, a, b))
        decreases(lambda remaining, index, a, b: remaining)
        a, b = b, a + b
        index = S(index)
        remaining = pred_or(0, remaining)
    return a


@theorem
def fib_loop_correct(n: Nat) -> Eq[Nat, fib_loop(n), fib_recursive(n)]:
    r"""Reuse the verified loop's specification for every natural input."""
    return verified_spec(fib_loop, n, MkUnit())


@theorem
def fib_loop_twice(n: Nat) -> Eq[Nat, add(fib_loop(n), fib_loop(n)), add(fib_recursive(n), fib_recursive(n))]:
    r"""Compose two reused specifications by congruence."""
    return cong2[Nat, Nat, Nat](lambda x: lambda y: add(x, y), verified_spec(fib_loop, n, MkUnit()), verified_spec(fib_loop, n, MkUnit()))
