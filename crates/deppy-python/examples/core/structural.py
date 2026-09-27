from deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons


@dependent(decreases="n")
def add(n: Nat, m: Nat) -> Nat:
    match n:
        case Z():
            return m
        case S(k):
            return S(add(k, m))


@dependent(decreases="xs")
def append[T: Type](n: Nat, m: Nat, xs: Vec[T, n], ys: Vec[T, m]) -> Vec[T, n + m]:
    match xs:
        case VNil():
            return ys
        case VCons(k, x, rest):
            return VCons(k + m, x, append(k, m, rest, ys))
