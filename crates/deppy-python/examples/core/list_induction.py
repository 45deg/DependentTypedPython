from __future__ import annotations
from deppy import inductive, constructor, dependent, Type, Nat, induct, Eq, refl


@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent
def length[A: Type](xs: List[A]) -> Nat:
    return induct(0, xs, lambda _: Nat, 0, lambda h, t, ih: 1)


@dependent
def test() -> Eq[Nat, length(Cons(0, Nil())), 1]:
    return refl(1)
