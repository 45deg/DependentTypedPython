from deppy import dependent, Nat, Z, S, Eq, refl
from deppy.indexed import IVec, INil, ICons, IFin, IFZ, IFS, get


@dependent
def first() -> Eq[Nat, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]())), IFZ(S(Z()))), 7]:
    return refl(7)


@dependent
def second() -> Eq[Nat, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]())), IFS(S(Z()), IFZ(Z()))), 9]:
    return refl(9)
