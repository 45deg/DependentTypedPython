from __future__ import annotations
from deppy import inductive, constructor, dependent, Type, Nat, induct, Eq, refl


@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent(decreases='xs')
def length[A: Type](xs: List[A]) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(h, t):
            return length(t)


@dependent
def proof() -> Eq[Nat, length(Cons(0, Nil())), 0]:
    return refl(0)
