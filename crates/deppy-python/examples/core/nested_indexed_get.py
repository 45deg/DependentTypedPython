from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Eq, refl, absurd
from deppy.indexed import IVec, INil, ICons, IFin, IFZ, IFS


@dependent(decreases='xs')
def get[A: Type, n: Nat](xs: IVec[A, n], i: IFin[n]) -> A:
    match xs:
        case INil():
            return absurd(A, i)
        case ICons(k, head, tail):
            match i:
                case IFZ(j):
                    return head
                case IFS(j, pred):
                    return get(tail, pred)


@dependent
def proof() -> Eq[Nat, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]())), IFS(S(Z()), IFZ(Z()))), 9]:
    return refl(9)
