from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Eq, refl
from deppy.indexed import IVec, INil, ICons

@dependent(decreases='xs')
def head[A: Type](n: Nat, xs: IVec[A, S(n)]) -> A:
    match xs:
        case ICons(k, h, tail):
            return h

@dependent(decreases='xs')
def empty[A: Type](xs: IVec[A, Z()]) -> Nat:
    match xs:
        case INil():
            return 0

@dependent(decreases='xs')
def second[A: Type](xs: IVec[A, S(S(Z()))]) -> A:
    match xs:
        case ICons(k, h, tail):
            match tail:
                case ICons(j, next, rest):
                    return head(Z(), tail)

@dependent(decreases='xs')
def last[A: Type](n: Nat, xs: IVec[A, S(n)]) -> A:
    match xs:
        case ICons(k, h, tail):
            match tail:
                case INil():
                    return h
                case ICons(j, next, rest):
                    return last(j, tail)

@dependent
def proof() -> Eq[Nat, second(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]()))), 9]:
    return refl(9)

@dependent
def last_proof() -> Eq[Nat, last(S(Z()), ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]()))), 9]:
    return refl(9)
