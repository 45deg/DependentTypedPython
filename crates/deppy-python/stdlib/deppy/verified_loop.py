from __future__ import annotations
from deppy._builtins import invariant, decreases, dependent, theorem, Sigma, Type, Pi, Nat, Z, S, Eq, refl, absurd
from deppy.data import Bool, False_, True_
from deppy.nat_order import LE, LT, le_refl, le_pred, le_trans
from deppy.verified import select, select_post_eq


@dependent(decreases="fuel")
def iterate[A: Type](guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: A], fuel: Nat, state: A) -> A:
    r"""Execute at most :math:`f` iterations, stopping early when the guard is false."""
    match fuel:
        case Z():
            return state
        case S(k):
            return select[A](guard(state), state, iterate(guard, step, k, step(state)))


@dependent
def LoopVC[A: Type, guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: A], measure: Pi[A, lambda _: Nat], invariant: Pi[A, lambda _: Type], post: Pi[A, lambda _: Type], initial: A]() -> Type:
    r"""Four nested pair fields: initialization, preservation, decrease, and exit.

    ``decrease`` proves :math:`m(\operatorname{step}(s)) < m(s)` when the
    invariant holds and the guard is true. ``exit`` establishes the
    postcondition when the invariant holds and the guard is false.
    """
    return Sigma[invariant(initial), lambda init:
        Sigma[Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: invariant(step(s))]]], lambda preserve:
        Sigma[Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: LT(measure(step(s)), measure(s))]]], lambda decrease:
        Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), False_()], lambda test: post(s)]]]]]]


@theorem(decreases="fuel")
def iterate_invariant[A: Type, invariant: Pi[A, lambda _: Type]](
    guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: A],
    preserve: Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: invariant(step(s))]]],
    fuel: Nat, state: A, inv: invariant(state),
) -> invariant(iterate(guard, step, fuel, state)):
    r"""Invariant preservation across :math:`f` bounded iterations."""
    match fuel:
        case Z():
            return inv
        case S(k):
            return select_post_eq[A, invariant](guard(state), state, iterate(guard, step, k, step(state)), lambda test: inv, lambda test: iterate_invariant(guard, step, preserve, k, step(state), preserve(state)(inv)(test)))


@theorem(decreases="flag")
def false_at_zero[A: Type](
    flag: Bool, state: A, measure: Pi[A, lambda _: Nat], step: Pi[A, lambda _: A],
    bound: LE[measure(state), 0],
    decrease: Pi[Eq[Bool, flag, True_()], lambda _: LT(measure(step(state)), measure(state))],
) -> Eq[Bool, flag, False_()]:
    r"""A nonnegative strictly decreasing measure rules out a true guard at zero."""
    match flag:
        case False_():
            return refl(False_())
        case True_():
            return absurd(Eq[Bool, True_(), False_()], le_trans(decrease(refl(True_())), 0, bound))


@theorem(decreases="fuel")
def iterate_exit[A: Type, invariant: Pi[A, lambda _: Type]](
    guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: A], measure: Pi[A, lambda _: Nat],
    preserve: Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: invariant(step(s))]]],
    decrease: Pi[A, lambda s: Pi[invariant(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: LT(measure(step(s)), measure(s))]]],
    fuel: Nat, state: A, inv: invariant(state), bound: LE[measure(state), fuel],
) -> Eq[Bool, guard(iterate(guard, step, fuel, state)), False_()]:
    r"""The guard is false after :math:`f` iterations when :math:`m(s) \le f`."""
    match fuel:
        case Z():
            return false_at_zero[A](guard(state), state, measure, step, bound, lambda test: decrease(state)(inv)(test))
        case S(k):
            return select_post_eq[A, lambda end: Eq[Bool, guard(end), False_()]](guard(state), state, iterate(guard, step, k, step(state)), lambda test: test, lambda test: iterate_exit(guard, step, measure, preserve, decrease, k, step(state), preserve(state)(inv)(test), le_pred(measure(step(state)), k, le_trans(decrease(state)(inv)(test), S(k), bound))))


@theorem
def loop_correct[A: Type, guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: A], measure: Pi[A, lambda _: Nat], invariant: Pi[A, lambda _: Type], post: Pi[A, lambda _: Type], initial: A](
    vc: LoopVC[A, guard, step, measure, invariant, post, initial],
) -> post(iterate(guard, step, measure(initial), initial)):
    r"""Derive the loop postcondition from all four checked obligations.

    :math:`I(s_0)`, preservation, and strict natural-number decrease imply
    that the bounded interpretation reaches a false guard and satisfies :math:`Q`.
    """
    return vc.snd.snd.snd(iterate(guard, step, measure(initial), initial))(iterate_invariant(guard, step, vc.snd.fst, measure(initial), initial, vc.fst))(iterate_exit(guard, step, measure, vc.snd.fst, vc.snd.snd.fst, measure(initial), initial, vc.fst, le_refl(measure(initial))))
