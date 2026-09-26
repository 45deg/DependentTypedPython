from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, theorem, absurd, Nat, Z, S, Eq, refl
from deppy.equality import cong
from deppy.data import Bool, False_, True_
from deppy.nat import add as nat_add, mul as nat_mul
from deppy.arithmetic import sub as nat_sub, divmod as nat_divmod
from deppy.verified import verified, Refined, select, nat_eq, nat_le, nat_lt, bool_eq, nat_eq_true, false_ne_true


@inductive
class Int:
    """Canonical signed integers: Pos(n) = n; Neg(n) = -(n + 1)."""
    @constructor
    def Pos(value: Nat) -> Int: ...
    @constructor
    def Neg(predecessor: Nat) -> Int: ...


@dependent
def of_nat(n: Nat) -> Int:
    return Pos(n)


@dependent
def negative_nat(n: Nat) -> Int:
    match n:
        case Z():
            return Pos(0)
        case S(k):
            return Neg(k)


@dependent
def magnitude(n: Int) -> Nat:
    match n:
        case Pos(k):
            return k
        case Neg(k):
            return S(k)


@dependent
def negative(n: Int) -> Bool:
    match n:
        case Pos(_):
            return False_()
        case Neg(_):
            return True_()


@dependent
def neg(n: Int) -> Int:
    match n:
        case Pos(k):
            return negative_nat(k)
        case Neg(k):
            return Pos(S(k))


@dependent
def pred_nat(k: Nat) -> Int:
    match k:
        case Z():
            return Neg(0)
        case S(j):
            return Pos(j)


@dependent
def pred(n: Int) -> Int:
    match n:
        case Pos(k):
            return pred_nat(k)
        case Neg(k):
            return Neg(S(k))


@dependent(decreases="b")
def difference(b: Nat, a: Nat) -> Int:
    match b:
        case Z():
            return Pos(a)
        case S(k):
            return pred(difference(k, a))


@dependent
def add(a: Int, b: Int) -> Int:
    match a:
        case Pos(n):
            match b:
                case Pos(m):
                    return Pos(nat_add(n, m))
                case Neg(m):
                    return difference(S(m), n)
        case Neg(n):
            match b:
                case Pos(m):
                    return difference(S(n), m)
                case Neg(m):
                    return Neg(S(nat_add(n, m)))


@dependent
def sub(a: Int, b: Int) -> Int:
    return add(a, neg(b))


@dependent
def mul(a: Int, b: Int) -> Int:
    return select[Int](bool_eq(negative(a), negative(b)), negative_nat(nat_mul(magnitude(a), magnitude(b))), Pos(nat_mul(magnitude(a), magnitude(b))))


@dependent
def le(a: Int, b: Int) -> Bool:
    match a:
        case Pos(n):
            match b:
                case Pos(m):
                    return nat_le(n, m)
                case Neg(_):
                    return False_()
        case Neg(n):
            match b:
                case Pos(_):
                    return True_()
                case Neg(m):
                    return nat_le(m, n)


@dependent
def lt(a: Int, b: Int) -> Bool:
    match a:
        case Pos(n):
            match b:
                case Pos(m):
                    return nat_lt(n, m)
                case Neg(_):
                    return False_()
        case Neg(n):
            match b:
                case Pos(_):
                    return True_()
                case Neg(m):
                    return nat_lt(m, n)


@dependent
def eq(a: Int, b: Int) -> Bool:
    match a:
        case Pos(n):
            match b:
                case Pos(m):
                    return nat_eq(n, m)
                case Neg(_):
                    return False_()
        case Neg(n):
            match b:
                case Pos(_):
                    return False_()
                case Neg(m):
                    return nat_eq(n, m)


@dependent
def quotient(a: Int, b: Int) -> Int:
    qr = nat_divmod(magnitude(a), magnitude(b))
    return select[Int](bool_eq(negative(a), negative(b)), negative_nat(nat_add(qr.fst, select[Nat](nat_eq(qr.snd, 0), 1, 0))), Pos(qr.fst))


@dependent
def remainder(a: Int, b: Int) -> Int:
    qr = nat_divmod(magnitude(a), magnitude(b))
    r = select[Nat](bool_eq(negative(a), negative(b)), select[Nat](nat_eq(qr.snd, 0), nat_sub(magnitude(b), qr.snd), 0), qr.snd)
    return select[Int](negative(b), Pos(r), negative_nat(r))


@verified
def to_nat(n: Refined[Int, lambda n: Eq[Bool, le(Pos(0), n), True_()]]) -> Refined[Nat, lambda r: Eq[Nat, r, magnitude(n)]]:
    return magnitude(n)


@theorem
def eq_true(a: Int, b: Int, test: Eq[Bool, eq(a, b), True_()]) -> Eq[Int, a, b]:
    match a:
        case Pos(n):
            match b:
                case Pos(m):
                    return cong(lambda x: Pos(x), nat_eq_true(n, m, test))
                case Neg(m):
                    return absurd(Eq[Int, Pos(n), Neg(m)], false_ne_true(test))
        case Neg(n):
            match b:
                case Pos(m):
                    return absurd(Eq[Int, Neg(n), Pos(m)], false_ne_true(test))
                case Neg(m):
                    return cong(lambda x: Neg(x), nat_eq_true(n, m, test))
