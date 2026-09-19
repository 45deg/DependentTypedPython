from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, fin0_elim, Eq, refl


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


@dependent(decreases="xs")
def snoc[T: Type](n: Nat, x: T, xs: Vec[T, n]) -> Vec[T, S(n)]:
    match xs:
        case VNil():
            return VCons(0, x, VNil())
        case VCons(k, head, rest):
            return VCons(S(k), head, snoc(k, x, rest))


@dependent(decreases="xs")
def reverse[T: Type](n: Nat, xs: Vec[T, n]) -> Vec[T, n]:
    match xs:
        case VNil():
            return VNil()
        case VCons(k, x, rest):
            return snoc(k, x, reverse(k, rest))


@dependent(decreases="n")
def last(n: Nat) -> Fin[S(n)]:
    match n:
        case Z():
            return FZ(0)
        case S(k):
            return FS(S(k), last(k))


@dependent(decreases="i")
def weaken(n: Nat, i: Fin[n]) -> Fin[S(n)]:
    match i:
        case FZ(k):
            return FZ(S(k))
        case FS(k, j):
            return FS(S(k), weaken(k, j))


@dependent(decreases="i")
def mirror(n: Nat, i: Fin[n]) -> Fin[n]:
    match i:
        case FZ(k):
            return last(k)
        case FS(k, j):
            return weaken(k, mirror(k, j))


@dependent(decreases="xs")
def get_snoc_last[T: Type](n: Nat, x: T, xs: Vec[T, n]) -> Eq[
    T, get(S(n), snoc(n, x, xs), last(n)), x,
]:
    match xs:
        case VNil():
            return refl(x)
        case VCons(k, head, rest):
            return get_snoc_last(k, x, rest)


@dependent(decreases="xs")
def get_snoc_weaken[T: Type](n: Nat, x: T, xs: Vec[T, n], i: Fin[n]) -> Eq[
    T, get(S(n), snoc(n, x, xs), weaken(n, i)), get(n, xs, i),
]:
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, head, rest):
            match i:
                case FZ(_):
                    return refl(head)
                case FS(_, j):
                    return get_snoc_weaken(k, x, rest, j)
