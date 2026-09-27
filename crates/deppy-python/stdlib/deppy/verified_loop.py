from deppy._builtins import invariant, decreases, dependent, theorem, Sigma, Type, Pi, Nat, Z, S, Eq, refl, absurd
from deppy.data import Bool, False_, True_, Sum, Left, Right, sum_elim, Unit
from deppy.nat_order import LE, LT, le_refl, le_pred, le_trans, pred_lt, lt_decide
from deppy.verified import select, select_post_eq, nat_lt, nat_lt_true, and_left, and_right, decision_true_intro
from deppy.nat import add, pred_or


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


@dependent(decreases="outcome", motive_level=1)
def outcome_post[A: Type, B: Type](next_post: Pi[A, lambda _: Type], done_post: Pi[B, lambda _: Type], outcome: Sum[A, Sigma[B, lambda _: Unit]]) -> Type:
    """Separate the obligations for another iteration and an early result."""
    match outcome:
        case Left(state):
            return next_post(state)
        case Right(result):
            return done_post(result.fst)


@theorem(decreases="outcome", motive_level=1)
def outcome_correct[A: Type, B: Type, C: Type, P: Pi[C, lambda _: Type]](
    outcome: Sum[A, Sigma[B, lambda _: Unit]], next: Pi[A, lambda _: C], done: Pi[B, lambda _: C],
    next_post: Pi[A, lambda _: Type], done_post: Pi[B, lambda _: Type],
    next_proof: Pi[A, lambda s: Pi[next_post(s), lambda _: P(next(s))]],
    done_proof: Pi[B, lambda r: Pi[done_post(r), lambda _: P(done(r))]],
    evidence: outcome_post[A, B](next_post, done_post, outcome),
) -> P(sum_elim[A, Sigma[B, lambda _: Unit], C](outcome, next, lambda payload: done(payload.fst))):
    """Eliminate a checked control outcome without confusing its two exits."""
    match outcome:
        case Left(state):
            return next_proof(state)(evidence)
        case Right(result):
            return done_proof(result.fst)(evidence)


@dependent(decreases="fuel")
def run[A: Type, B: Type](guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: Sum[A, Sigma[B, lambda _: Unit]]], finish: Pi[A, lambda _: B], fuel: Nat, state: A) -> B:
    """Bounded loop with a distinct early-result outcome, including at fuel zero."""
    match fuel:
        case Z():
            return select[B](guard(state), finish(state), sum_elim(step(state), finish, lambda payload: payload.fst))
        case S(k):
            return select[B](guard(state), finish(state), sum_elim(step(state), lambda next: run(guard, step, finish, k, next), lambda payload: payload.fst))


@theorem(decreases="fuel")
def run_correct[A: Type, B: Type, I: Pi[A, lambda _: Type], P: Pi[B, lambda _: Type]](
    guard: Pi[A, lambda _: Bool], step: Pi[A, lambda _: Sum[A, Sigma[B, lambda _: Unit]]], finish: Pi[A, lambda _: B], measure: Pi[A, lambda _: Nat],
    advance: Pi[A, lambda s: Pi[I(s), lambda inv: Pi[Eq[Bool, guard(s), True_()], lambda test: outcome_post(lambda next: Sigma[I(next), lambda _: LT(measure(next), measure(s))], P, step(s))]]],
    exit: Pi[A, lambda s: Pi[I(s), lambda inv: Pi[Eq[Bool, guard(s), False_()], lambda test: P(finish(s))]]],
    fuel: Nat, state: A, inv: I(state), bound: LE[measure(state), fuel],
) -> P(run(guard, step, finish, fuel, state)):
    """Prove ordinary exits and early results, checking decrease only on backedges."""
    match fuel:
        case Z():
            return select_post_eq[B, P](guard(state), finish(state), sum_elim(step(state), finish, lambda payload: payload.fst), lambda test: exit(state)(inv)(test), lambda test: outcome_correct[A, B, B, P](step(state), finish, lambda result: result, lambda next: Sigma[I(next), lambda _: LT(measure(next), measure(state))], P, lambda next, evidence: absurd(P(finish(next)), le_trans(evidence.snd, 0, bound)), lambda result, evidence: evidence, advance(state)(inv)(test)))
        case S(k):
            return select_post_eq[B, P](guard(state), finish(state), sum_elim(step(state), lambda next: run(guard, step, finish, k, next), lambda payload: payload.fst), lambda test: exit(state)(inv)(test), lambda test: outcome_correct[A, B, B, P](step(state), lambda next: run(guard, step, finish, k, next), lambda result: result, lambda next: Sigma[I(next), lambda _: LT(measure(next), measure(state))], P, lambda next, evidence: run_correct(guard, step, finish, measure, advance, exit, k, next, evidence.fst, le_pred(measure(next), k, le_trans(evidence.snd, S(k), bound))), lambda result, evidence: evidence, advance(state)(inv)(test)))


@dependent(decreases="amount")
def range_sub(amount: Nat, value: Nat) -> Nat:
    """Internal saturated decrement used by descending Nat ranges."""
    match amount:
        case Z():
            return value
        case S(k):
            return range_sub(k, pred_or(0, value))


@dependent
def range_next(cursor: Nat, stride: Nat, descending: Bool) -> Nat:
    """Advance a private range cursor; the body cannot modify it."""
    return select[Nat](descending, add(cursor, stride), range_sub(stride, cursor))


@dependent(decreases="fuel")
def range_count_fuel(fuel: Nat, cursor: Nat, stop: Nat, stride: Nat, descending: Bool) -> Nat:
    """Count a Nat range within its endpoint bound, for a positive stride."""
    match fuel:
        case Z():
            return 0
        case S(k):
            return select[Nat](select[Bool](descending, nat_lt(cursor, stop), nat_lt(stop, cursor)), 0, S(range_count_fuel(k, range_next(cursor, stride, descending), stop, stride, descending)))


@dependent
def range_count(start: Nat, stop: Nat, stride: Nat, descending: Bool) -> Nat:
    """A positive-stride Nat range has at most stop (ascending) or start steps."""
    return range_count_fuel(select[Nat](descending, stop, start), start, stop, stride, descending)


@theorem
def range_bound(count: Nat, a: Nat, b: Nat, test: Eq[Bool, select[Bool](nat_lt(0, count), False_(), nat_lt(a, b)), True_()]) -> Eq[Bool, nat_lt(a, b), True_()]:
    """Recover the source range bound at an iteration entry."""
    return and_right(nat_lt(0, count), nat_lt(a, b), test)


@theorem
def range_decrease(count: Nat, a: Nat, b: Nat, test: Eq[Bool, select[Bool](nat_lt(0, count), False_(), nat_lt(a, b)), True_()]) -> LT(pred_or(0, count), count):
    """The private iteration budget strictly decreases on every backedge."""
    return pred_lt(count, nat_lt_true(0, count, and_left(nat_lt(0, count), nat_lt(a, b), test)))


@theorem
def positive_stride(n: Nat, positive: LT(0, n)) -> Eq[Bool, nat_lt(0, n), True_()]:
    """A positive Nat stride satisfies the generated range precondition."""
    return decision_true_intro(lt_decide(0, n), positive)
