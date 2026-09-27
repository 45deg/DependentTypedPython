from __future__ import annotations
from deppy import inductive, constructor, dependent, Type, Nat, Eq, refl

@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent(decreases='xs')
def pairs[A: Type](xs: List[A]) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(_, Nil()):
            return 0
        case Cons(_, Cons(_, rest)):
            return pairs(rest)

@dependent
def choose[A: Type](xs: List[A]) -> Nat:
    match xs:
        case Cons(_, Cons(_, Nil())):
            return 2
        case Cons(_, _):
            return 1
        case Nil():
            return 0

@dependent
def proof() -> Eq[Nat, pairs(Cons(0, Cons(0, Cons(0, Cons(0, Nil()))))), 0]:
    return refl(0)

@dependent
def selected() -> Eq[Nat, choose(Cons(0, Cons(0, Nil()))), 2]:
    return refl(2)
