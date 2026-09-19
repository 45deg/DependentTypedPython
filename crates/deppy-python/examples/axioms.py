from __future__ import annotations
from deppy import axiom, dependent, Type, Pi, Eq
from deppy.equality import sym


@axiom
def funext[A: Type, B: Type](
    f: Pi[A, lambda x: B],
    g: Pi[A, lambda x: B],
    pointwise: Pi[A, lambda x: Eq[B, f(x), g(x)]],
) -> Eq[Pi[A, lambda x: B], f, g]:
    ...


@dependent
def pointwise_equal_symmetric[A: Type, B: Type](
    f: Pi[A, lambda x: B],
    g: Pi[A, lambda x: B],
    pointwise: Pi[A, lambda x: Eq[B, f(x), g(x)]],
) -> Eq[Pi[A, lambda x: B], g, f]:
    return sym(funext(f, g, pointwise))
