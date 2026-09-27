from __future__ import annotations

from deppy import theorem, Type, Pi, Sigma, Eq
from deppy.equality import sym
from deppy.data import Empty
from deppy.bool import Bool, False_, True_, negate, true_ne_false


@theorem(decreases="b")
def negate_no_fixed_point(b: Bool, equal: Eq[Bool, negate(b), b]) -> Empty:
    """No Boolean equals its negation."""
    match b:
        case False_():
            return true_ne_false(equal)
        case True_():
            return true_ne_false(sym(equal))


@theorem
def cantor[A: Type](
    f: Pi[A, lambda _: Pi[A, lambda _: Bool]],
    onto: Pi[
        Pi[A, lambda _: Bool],
        lambda g: Sigma[A, lambda a: Pi[A, lambda x: Eq[Bool, f(a)(x), g(x)]]],
    ],
) -> Empty:
    """Cantor's theorem: no map A -> (A -> Bool) is surjective.

    The diagonal function disagrees with f(a) at a for every a.
    Surjectivity would produce an a where they agree, a contradiction.
    """
    witness = onto(lambda x: negate(f(x)(x)))
    a = witness.fst
    equal = witness.snd(a)
    return negate_no_fixed_point(f(a)(a), sym(equal))
