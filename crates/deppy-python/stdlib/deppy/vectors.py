from __future__ import annotations
from deppy._builtins import dependent, theorem, Type, Pi, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, fin0_elim, Eq, refl
from deppy.equality import trans
from deppy.nat import add
from deppy.fin import fin_case


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
def map[A: Type, B: Type](n: Nat, f: Pi[A, lambda _: B], xs: Vec[A, n]) -> Vec[B, n]:
    """Map a vector without changing its size."""
    match xs:
        case VNil():
            return VNil()
        case VCons(k, x, rest):
            return VCons(k, f(x), map(k, f, rest))


@theorem(decreases="xs")
def get_map[A: Type, B: Type](n: Nat, f: Pi[A, lambda _: B], xs: Vec[A, n], i: Fin[n]) -> Eq[
    B, get(n, map(n, f, xs), i), f(get(n, xs, i))
]:
    """Reading a mapped vector applies the map to the original element."""
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, x, rest):
            match i:
                case FZ(_):
                    return refl(f(x))
                case FS(_, j):
                    return get_map(k, f, rest, j)


@dependent(decreases="xs")
def append[T: Type](n: Nat, m: Nat, xs: Vec[T, n], ys: Vec[T, m]) -> Vec[T, add(n, m)]:
    """Concatenate two vectors; the result size is the sum of their sizes."""
    match xs:
        case VNil():
            return ys
        case VCons(k, x, rest):
            return VCons(add(k, m), x, append(k, m, rest, ys))


@dependent(decreases="i")
def append_left_index(n: Nat, m: Nat, i: Fin[n]) -> Fin[add(n, m)]:
    """Embed an index of the left vector into a concatenation."""
    match i:
        case FZ(k):
            return FZ(add(k, m))
        case FS(k, j):
            return FS(add(k, m), append_left_index(k, m, j))


@dependent(decreases="n")
def append_right_index(n: Nat, m: Nat, j: Fin[m]) -> Fin[add(n, m)]:
    """Shift an index of the right vector past the left vector."""
    match n:
        case Z():
            return j
        case S(k):
            return FS(add(k, m), append_right_index(k, m, j))


@theorem(decreases="xs")
def get_append_left[T: Type](n: Nat, m: Nat, xs: Vec[T, n], ys: Vec[T, m], i: Fin[n]) -> Eq[
    T, get(add(n, m), append(n, m, xs, ys), append_left_index(n, m, i)), get(n, xs, i)
]:
    """Reading the left part of a concatenation returns the original element."""
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, x, rest):
            return fin_case(k, lambda q: Eq[
                T, get(add(S(k), m), append(S(k), m, xs, ys), append_left_index(S(k), m, q)),
                get(S(k), xs, q)
            ], i, refl(x), lambda j: get_append_left(k, m, rest, ys, j))


@theorem(decreases="xs")
def get_append_right[T: Type](n: Nat, m: Nat, xs: Vec[T, n], ys: Vec[T, m], j: Fin[m]) -> Eq[
    T, get(add(n, m), append(n, m, xs, ys), append_right_index(n, m, j)), get(m, ys, j)
]:
    """Reading the right part of a concatenation returns the original element."""
    match xs:
        case VNil():
            return refl(get(m, ys, j))
        case VCons(k, x, rest):
            return get_append_right(k, m, rest, ys, j)


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


@theorem(decreases="xs")
def reverse_get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> Eq[
    T, get(n, reverse(n, xs), mirror(n, i)), get(n, xs, i)
]:
    """Reversal reads the original element at the mirrored index."""
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
