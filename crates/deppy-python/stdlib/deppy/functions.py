from __future__ import annotations
from deppy._builtins import record, dependent, theorem, Type, Pi, Sigma, Pair, Eq, refl
from deppy.equality import sym, trans, cong


@record
class Bijection[A: Type, B: Type]:
    """A map with an explicit inverse and both inverse laws."""
    forward: Pi[A, lambda _: B]
    backward: Pi[B, lambda _: A]
    left_inverse: Pi[A, lambda x: Eq[A, self.backward(self.forward(x)), x]]
    right_inverse: Pi[B, lambda y: Eq[B, self.forward(self.backward(y)), y]]


@dependent
def identity_bijection[A: Type]() -> Bijection[A, A]:
    return Bijection[A, A](lambda x: x, lambda x: x, lambda x: refl(x), lambda x: refl(x))


@dependent
def inverse_bijection[A: Type, B: Type](b: Bijection[A, B]) -> Bijection[B, A]:
    return Bijection[B, A](b.backward, b.forward, b.right_inverse, b.left_inverse)


@dependent
def compose_bijection[A: Type, B: Type, C: Type](first: Bijection[A, B], second: Bijection[B, C]) -> Bijection[A, C]:
    """Composition preserves explicit left and right inverses."""
    return Bijection[A, C](
        lambda x: second.forward(first.forward(x)),
        lambda z: first.backward(second.backward(z)),
        lambda x: trans(
            cong(first.backward, second.left_inverse(first.forward(x))),
            first.left_inverse(x),
        ),
        lambda z: trans(
            cong(second.forward, first.right_inverse(second.backward(z))),
            second.right_inverse(z),
        ),
    )


@theorem
def bijection_injective[A: Type, B: Type](b: Bijection[A, B], x: A, y: A,
                                          equal: Eq[B, b.forward(x), b.forward(y)]) -> Eq[A, x, y]:
    """A bijection's forward map is injective."""
    return trans(sym(b.left_inverse(x)), trans(cong(b.backward, equal), b.left_inverse(y)))


@dependent
def bijection_surjective[A: Type, B: Type](b: Bijection[A, B], y: B) -> Sigma[
    A, lambda x: Eq[B, b.forward(x), y]
]:
    """The backward map supplies a preimage of every target value."""
    return Pair(b.backward(y), b.right_inverse(y))
