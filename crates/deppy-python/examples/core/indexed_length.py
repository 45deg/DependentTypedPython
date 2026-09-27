from deppy import dependent, Type, Nat, Z, S, Eq, refl
from deppy.indexed import IVec, INil, ICons


@dependent(decreases='xs')
def length[A: Type](n: Nat, xs: IVec[A, n]) -> Nat:
    match xs:
        case INil():
            return 0
        case ICons(k, _, tail):
            return S(length(k, tail))


@dependent
def proof() -> Eq[Nat, length(S(Z()), ICons(Z(), 7, INil[Nat]())), 1]:
    return refl(1)
