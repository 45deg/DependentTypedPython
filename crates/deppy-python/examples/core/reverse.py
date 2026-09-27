from __future__ import annotations
from deppy import dependent, Type, Nat, Eq, trans, Fin, FZ, FS, fin0_elim, Vec, VNil, VCons
from deppy.vectors import get, reverse, mirror, get_snoc_last, get_snoc_weaken


@dependent(decreases="xs")
def reverse_get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> Eq[
    T, get(n, reverse(n, xs), mirror(n, i)), get(n, xs, i),
]:
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, x, rest):
            match i:
                case FZ(_):
                    return get_snoc_last(k, x, reverse(k, rest))
                case FS(_, j):
                    return trans(
                        get_snoc_weaken(k, x, reverse(k, rest), mirror(k, j)),
                        reverse_get(k, rest, j),
                    )
