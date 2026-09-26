from __future__ import annotations
from deppy._builtins import dependent, theorem, Nat, Z, S, Eq, refl
from deppy.equality import sym, trans, cong, cong2, transport

# Nat and its eliminator are supplied by the frontend's builtin registry.  The
# operations below deliberately keep the computation rules used by the
# original finite-mathematics examples: add recurses on its first argument and
# mul on its second.


@dependent(decreases="n")
def add(n: Nat, m: Nat) -> Nat:
    r"""Natural-number addition, :math:`n + m`, recursive in ``n``."""
    match n:
        case Z():
            return m
        case S(k):
            return S(add(k, m))


@dependent(decreases="k")
def mul(n: Nat, k: Nat) -> Nat:
    r"""Natural-number multiplication, :math:`n k`, recursive in ``k``."""
    match k:
        case Z():
            return 0
        case S(j):
            return add(n, mul(n, j))


@dependent(decreases="n")
def add_zero(n: Nat) -> Eq[Nat, add(n, 0), n]:
    r"""Theorem ``add_zero``: :math:`n + 0 = n`."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return cong(lambda x: S(x), add_zero(k))


@dependent(decreases="n")
def add_succ(n: Nat, m: Nat) -> Eq[Nat, add(n, S(m)), S(add(n, m))]:
    r"""Theorem ``add_succ``: :math:`n + (m+1) = (n+m)+1`."""
    match n:
        case Z():
            return refl(S(m))
        case S(k):
            return cong(lambda x: S(x), add_succ(k, m))


@dependent(decreases="a")
def add_assoc(a: Nat, b: Nat, c: Nat) -> Eq[Nat, add(add(a, b), c), add(a, add(b, c))]:
    r"""Theorem ``add_assoc``: :math:`(a+b)+c = a+(b+c)`."""
    match a:
        case Z():
            return refl(add(b, c))
        case S(k):
            return cong(lambda x: S(x), add_assoc(k, b, c))


@dependent(decreases="a")
def add_comm(a: Nat, b: Nat) -> Eq[Nat, add(a, b), add(b, a)]:
    r"""Theorem ``add_comm``: :math:`a+b=b+a`."""
    match a:
        case Z():
            return sym(add_zero(b))
        case S(k):
            return trans(cong(lambda x: S(x), add_comm(k, b)), sym(add_succ(b, k)))


@dependent
def add_swap(a: Nat, b: Nat, c: Nat) -> Eq[Nat, add(a, add(b, c)), add(b, add(a, c))]:
    r"""Theorem ``add_swap``: :math:`a+(b+c)=b+(a+c)`."""
    return trans(sym(add_assoc(a, b, c)), trans(cong(lambda x: add(x, c), add_comm(a, b)), add_assoc(b, a, c)))


@dependent(decreases="n")
def mul_zero(n: Nat) -> Eq[Nat, mul(n, 0), 0]:
    r"""Theorem ``mul_zero``: :math:`n\,0=0`."""
    return refl(0)


@dependent(decreases="n")
def mul_one(n: Nat) -> Eq[Nat, mul(n, 1), n]:
    r"""Theorem ``mul_one``: :math:`n\,1=n`."""
    return add_zero(n)


@dependent(decreases="b")
def mul_add_right(a: Nat, b: Nat, c: Nat) -> Eq[Nat, mul(a, add(b, c)), add(mul(a, b), mul(a, c))]:
    r"""Right distributivity: :math:`a(b+c)=ab+ac`."""
    match b:
        case Z():
            return refl(mul(a, c))
        case S(k):
            return trans(
                cong(lambda x: add(a, x), mul_add_right(a, k, c)),
                sym(add_assoc(a, mul(a, k), mul(a, c))),
            )


@theorem(decreases="b")
def mul_succ_left(a: Nat, b: Nat) -> Eq[Nat, mul(S(a), b), add(b, mul(a, b))]:
    """Multiplying by a successor in the left argument."""
    match b:
        case Z():
            return refl(0)
        case S(k):
            return cong(lambda n: S(n), trans(
                cong(lambda n: add(a, n), mul_succ_left(a, k)),
                add_swap(a, k, mul(a, k)),
            ))


@theorem(decreases="n")
def zero_mul(n: Nat) -> Eq[Nat, mul(0, n), 0]:
    """Zero multiplied by any natural number is zero."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return zero_mul(k)


@theorem(decreases="b")
def mul_comm(a: Nat, b: Nat) -> Eq[Nat, mul(a, b), mul(b, a)]:
    """Natural-number multiplication is commutative."""
    match b:
        case Z():
            return sym(zero_mul(a))
        case S(k):
            return trans(
                cong(lambda n: add(a, n), mul_comm(a, k)),
                sym(mul_succ_left(k, a)),
            )


@theorem
def mul_add_left(a: Nat, b: Nat, c: Nat) -> Eq[Nat, mul(add(a, b), c), add(mul(a, c), mul(b, c))]:
    """Left distributivity of multiplication over addition."""
    return trans(mul_comm(add(a, b), c), trans(
        mul_add_right(c, a, b),
        cong2(add, mul_comm(c, a), mul_comm(c, b)),
    ))


@theorem(decreases="c")
def mul_assoc(a: Nat, b: Nat, c: Nat) -> Eq[Nat, mul(mul(a, b), c), mul(a, mul(b, c))]:
    """Natural-number multiplication is associative."""
    match c:
        case Z():
            return refl(0)
        case S(k):
            return trans(
                cong(lambda n: add(mul(a, b), n), mul_assoc(a, b, k)),
                sym(mul_add_right(a, b, mul(b, k))),
            )


@dependent
def pred_or(fallback: Nat, n: Nat) -> Nat:
    r"""Return the predecessor of ``n``, using ``fallback`` when :math:`n=0`."""
    match n:
        case Z():
            return fallback
        case S(k):
            return k


@dependent
def succ_injective(a: Nat, b: Nat, p: Eq[Nat, S(a), S(b)]) -> Eq[Nat, a, b]:
    r"""Theorem ``succ_injective``: :math:`a+1=b+1 \Rightarrow a=b`."""
    return transport[Nat, S(a), S(b)](lambda n: Eq[Nat, a, pred_or(a, n)], p, refl(a))


@dependent(decreases="a")
def add_left_cancel(a: Nat, b: Nat, c: Nat, p: Eq[Nat, add(a, b), add(a, c)]) -> Eq[Nat, b, c]:
    r"""Left cancellation: :math:`a+b=a+c \Rightarrow b=c`."""
    match a:
        case Z():
            return p
        case S(k):
            return add_left_cancel(k, b, c, succ_injective(add(k, b), add(k, c), p))


@dependent
def add_right_cancel(a: Nat, b: Nat, c: Nat, p: Eq[Nat, add(b, a), add(c, a)]) -> Eq[Nat, b, c]:
    r"""Right cancellation: :math:`b+a=c+a \Rightarrow b=c`."""
    return add_left_cancel(
        a, b, c,
        trans(add_comm(a, b), trans(p, sym(add_comm(a, c)))),
    )
