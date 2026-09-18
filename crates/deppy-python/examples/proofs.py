from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, fin0_elim, Eq, refl, cong


@dependent(decreases="xs")
def get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> T:
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, x, rest):
            match i:
                case FZ(_):
                    return x
                case FS(_, j):
                    return get(k, rest, j)


@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, n + 0, n]:
    match n:
        case Z():
            return refl(Z())
        case S(k):
            return cong(S, zero_right(k))
