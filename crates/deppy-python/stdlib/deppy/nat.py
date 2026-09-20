from __future__ import annotations
from deppy._builtins import dependent, Nat, Z, S, Eq, refl
from deppy.equality import sym, trans, cong, transport

# Nat and its eliminator are supplied by the frontend's builtin registry.  The
# operations below deliberately keep the computation rules used by the
# original finite-mathematics examples: add recurses on its first argument and
# mul on its second.


@dependent(decreases="n")
def add(n: Nat, m: Nat) -> Nat:
    match n:
        case Z():
            return m
        case S(k):
            return S(add(k, m))


@dependent(decreases="k")
def mul(n: Nat, k: Nat) -> Nat:
    match k:
        case Z():
            return 0
        case S(j):
            return add(n, mul(n, j))


@dependent(decreases="n")
def add_zero(n: Nat) -> Eq[Nat, add(n, 0), n]:
    match n:
        case Z():
            return refl(0)
        case S(k):
            return cong(lambda x: S(x), add_zero(k))


@dependent(decreases="n")
def add_succ(n: Nat, m: Nat) -> Eq[Nat, add(n, S(m)), S(add(n, m))]:
    match n:
        case Z():
            return refl(S(m))
        case S(k):
            return cong(lambda x: S(x), add_succ(k, m))


@dependent(decreases="a")
def add_assoc(a: Nat, b: Nat, c: Nat) -> Eq[Nat, add(add(a, b), c), add(a, add(b, c))]:
    match a:
        case Z():
            return refl(add(b, c))
        case S(k):
            return cong(lambda x: S(x), add_assoc(k, b, c))


@dependent(decreases="a")
def add_comm(a: Nat, b: Nat) -> Eq[Nat, add(a, b), add(b, a)]:
    match a:
        case Z():
            return sym(add_zero(b))
        case S(k):
            return trans(cong(lambda x: S(x), add_comm(k, b)), sym(add_succ(b, k)))


@dependent
def add_swap(a: Nat, b: Nat, c: Nat) -> Eq[Nat, add(a, add(b, c)), add(b, add(a, c))]:
    return trans(sym(add_assoc(a, b, c)), trans(cong(lambda x: add(x, c), add_comm(a, b)), add_assoc(b, a, c)))


@dependent(decreases="n")
def mul_zero(n: Nat) -> Eq[Nat, mul(n, 0), 0]:
    return refl(0)


@dependent(decreases="n")
def mul_one(n: Nat) -> Eq[Nat, mul(n, 1), n]:
    return add_zero(n)


@dependent(decreases="b")
def mul_add_right(a: Nat, b: Nat, c: Nat) -> Eq[Nat, mul(a, add(b, c)), add(mul(a, b), mul(a, c))]:
    match b:
        case Z():
            return refl(mul(a, c))
        case S(k):
            return trans(
                cong(lambda x: add(a, x), mul_add_right(a, k, c)),
                sym(add_assoc(a, mul(a, k), mul(a, c))),
            )


@dependent
def pred_or(fallback: Nat, n: Nat) -> Nat:
    match n:
        case Z():
            return fallback
        case S(k):
            return k


@dependent
def succ_injective(a: Nat, b: Nat, p: Eq[Nat, S(a), S(b)]) -> Eq[Nat, a, b]:
    return transport[Nat, S(a), S(b)](lambda n: Eq[Nat, a, pred_or(a, n)], p, refl(a))


@dependent(decreases="a")
def add_left_cancel(a: Nat, b: Nat, c: Nat, p: Eq[Nat, add(a, b), add(a, c)]) -> Eq[Nat, b, c]:
    match a:
        case Z():
            return p
        case S(k):
            return add_left_cancel(k, b, c, succ_injective(add(k, b), add(k, c), p))


@dependent
def add_right_cancel(a: Nat, b: Nat, c: Nat, p: Eq[Nat, add(b, a), add(c, a)]) -> Eq[Nat, b, c]:
    return add_left_cancel(
        a, b, c,
        trans(add_comm(a, b), trans(p, sym(add_comm(a, c)))),
    )
