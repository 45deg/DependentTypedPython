from __future__ import annotations
from deppy import inductive, constructor, dependent, Type, Nat, Eq, refl

@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent
def classify[A: Type](xs: List[A]) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(h, t):
            match t:
                case Nil():
                    return 1
                case Cons(j, rest):
                    match rest:
                        case Nil():
                            return 2
                        case Cons(k, tail):
                            return 3

@dependent
def proof() -> Eq[Nat, classify(Cons(0, Cons(0, Nil()))), 2]:
    return refl(2)
