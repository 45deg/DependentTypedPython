from deppy import dependent, Type, Nat, Z, S, Eq, refl, Vec, VNil, VCons


@dependent(decreases="n")
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    proof: Eq[Nat, n, n] = refl(n)
    match n:
        case Z():
            return proof
        case S(k):
            return proof


@dependent(decreases="xs")
def keep[T: Type](n: Nat, xs: Vec[T, n]) -> Vec[T, n]:
    saved: Vec[T, n] = xs
    again = saved
    match xs:
        case VNil():
            return again
        case VCons(k, head, tail):
            return again


@dependent(decreases="n")
def count(n: Nat) -> Nat:
    one = S(Z())
    match n:
        case Z():
            return Z()
        case S(k):
            previous = count(k)
            return one + previous
