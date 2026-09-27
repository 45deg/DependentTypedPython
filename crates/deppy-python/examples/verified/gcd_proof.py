from __future__ import annotations
from deppy import dependent, theorem, Nat, Z, S, Type, Pi, Sigma, Pair, Eq, refl, absurd
from deppy.data import Bool, False_, sum_elim
from deppy.equality import sym, trans, cong, transport
from deppy.nat import add, mul, add_zero, add_left_cancel, mul_one, zero_mul, mul_add_right, mul_assoc
from deppy.nat_order import LE, LT, LEZero, LESucc, le_refl, le_trans, le_total, le_lt_or_eq, lt_irrefl, mul_lt_mul_left
from deppy.arithmetic import quotient, remainder, divmod_equation
from deppy.verified import nat_lt, nat_lt_false_zero


@dependent
def Divides(d: Nat, n: Nat) -> Type:
    """A witness q with d * q = n; in particular, zero divides zero."""
    return Sigma[Nat, lambda q: Eq[Nat, mul(d, q), n]]


@dependent
def Common(d: Nat, a: Nat, b: Nat) -> Type:
    return Sigma[Divides(d, a), lambda _: Divides(d, b)]


@dependent
def IsGCD(a: Nat, b: Nat, g: Nat) -> Type:
    """g divides both inputs and every common divisor divides g."""
    return Sigma[Common(g, a, b), lambda _:
        Pi[Nat, lambda d: Pi[Common(d, a, b), lambda _: Divides(d, g)]]]


@theorem
def divides_self(n: Nat) -> Divides(n, n):
    return Pair(1, mul_one(n))


@theorem
def divides_zero(d: Nat) -> Divides(d, 0):
    return Pair(0, refl(0))


@theorem
def divides_add(d: Nat, a: Nat, b: Nat, da: Divides(d, a), db: Divides(d, b)) -> Divides(d, add(a, b)):
    return Pair(add(da.fst, db.fst),
        trans(mul_add_right(d, da.fst, db.fst),
            trans(cong(lambda x: add(x, mul(d, db.fst)), da.snd),
                  cong(lambda x: add(a, x), db.snd))))


@theorem
def divides_mul(d: Nat, a: Nat, k: Nat, proof: Divides(d, a)) -> Divides(d, mul(a, k)):
    return Pair(mul(proof.fst, k),
        trans(sym(mul_assoc(d, proof.fst, k)), cong(lambda x: mul(x, k), proof.snd)))


@theorem(decreases="n")
def le_add(n: Nat, m: Nat) -> LE[n, add(n, m)]:
    match n:
        case Z():
            return LEZero(m)
        case S(k):
            return LESucc(k, add(k, m), le_add(k, m))


@theorem(decreases="proof")
def le_difference[n: Nat, m: Nat](proof: LE[n, m]) -> Sigma[Nat, lambda k: Eq[Nat, add(n, k), m]]:
    match proof:
        case LEZero(k):
            return Pair(k, refl(k))
        case LESucc(a, b, rest):
            witness = le_difference(rest)
            return Pair(witness.fst, cong(lambda x: S(x), witness.snd))


@theorem
def mul_le_reflect(d: Nat, p: Nat, q: Nat, positive: LT(0, d), bound: LE[mul(d, p), mul(d, q)]) -> LE[p, q]:
    return sum_elim[LE[p, q], LE[q, p], LE[p, q]](le_total(p, q),
        lambda forward: forward,
        lambda backward: sum_elim[LT(q, p), Eq[Nat, q, p], LE[p, q]](le_lt_or_eq(backward),
            lambda strict: absurd(LE[p, q], lt_irrefl(mul(d, q), le_trans(mul_lt_mul_left(d, q, p, positive, strict), mul(d, q), bound))),
            lambda equal: transport[Nat, p, q](lambda r: LE[p, r], sym(equal), le_refl(p))))


@theorem
def divides_cancel_add_positive(d: Nat, a: Nat, b: Nat, positive: LT(0, d), whole: Divides(d, add(a, b)), part: Divides(d, a)) -> Divides(d, b):
    lower = transport[Nat, a, mul(d, part.fst)](
        lambda x: LE[x, add(a, b)], sym(part.snd), le_add(a, b))
    upper = transport[Nat, add(a, b), mul(d, whole.fst)](
        lambda x: LE[mul(d, part.fst), x], sym(whole.snd), lower)
    difference = le_difference(mul_le_reflect(d, part.fst, whole.fst, positive, upper))
    distributed = trans(sym(mul_add_right(d, part.fst, difference.fst)),
        cong(lambda x: mul(d, x), difference.snd))
    equation = trans(sym(cong(lambda x: add(x, mul(d, difference.fst)), part.snd)),
        trans(distributed, whole.snd))
    return Pair(difference.fst, add_left_cancel(a, mul(d, difference.fst), b, equation))


@theorem
def divides_cancel_add_zero(a: Nat, b: Nat, whole: Divides(0, add(a, b)), part: Divides(0, a)) -> Divides(0, b):
    equation = trans(add_zero(a), trans(sym(part.snd),
        trans(zero_mul(part.fst), trans(sym(zero_mul(whole.fst)), whole.snd))))
    return Pair(0, add_left_cancel(a, 0, b, equation))


@theorem(decreases="d")
def divides_cancel_add(d: Nat, a: Nat, b: Nat, whole: Divides(d, add(a, b)), part: Divides(d, a)) -> Divides(d, b):
    """Cancellation for divisibility, including the zero-divisor case."""
    match d:
        case Z():
            return divides_cancel_add_zero(a, b, whole, part)
        case S(k):
            return divides_cancel_add_positive(S(k), a, b, LESucc(0, k, LEZero(k)), whole, part)


@theorem
def euclid_forward(d: Nat, a: Nat, b: Nat, common: Common(d, a, b)) -> Common(d, b, remainder(a, b)):
    """Every old common divisor divides the new pair."""
    q = quotient(a, b)
    r = remainder(a, b)
    equation = divmod_equation(a, b)
    whole = transport[Nat, a, add(mul(b, q), r)](lambda n: Divides(d, n), sym(equation), common.fst)
    part = divides_mul(d, b, q, common.snd)
    return Pair(common.snd, divides_cancel_add(d, mul(b, q), r, whole, part))


@theorem
def euclid_backward(d: Nat, a: Nat, b: Nat, common: Common(d, b, remainder(a, b))) -> Common(d, a, b):
    """Every new common divisor divides the old pair."""
    q = quotient(a, b)
    r = remainder(a, b)
    sum_proof = divides_add(d, mul(b, q), r, divides_mul(d, b, q, common.fst), common.snd)
    return Pair(transport[Nat, add(mul(b, q), r), a](lambda n: Divides(d, n), divmod_equation(a, b), sum_proof), common.fst)


@dependent
def CommonEquiv(a: Nat, b: Nat, x: Nat, y: Nat) -> Type:
    """The current pair has exactly the original pair's common divisors."""
    return Pi[Nat, lambda d: Sigma[
        Pi[Common(d, a, b), lambda _: Common(d, x, y)],
        lambda _: Pi[Common(d, x, y), lambda _: Common(d, a, b)]]]


@theorem
def common_equiv_initial(a: Nat, b: Nat) -> CommonEquiv(a, b, a, b):
    return lambda d: Pair(lambda proof: proof, lambda proof: proof)


@theorem
def common_equiv_step(a: Nat, b: Nat, x: Nat, y: Nat, invariant: CommonEquiv(a, b, x, y)) -> CommonEquiv(a, b, y, remainder(x, y)):
    return lambda d: Pair(
        lambda proof: euclid_forward(d, x, y, invariant(d).fst(proof)),
        lambda proof: invariant(d).snd(euclid_backward(d, x, y, proof)))


@theorem
def gcd_exit(a: Nat, b: Nat, x: Nat, y: Nat, invariant: CommonEquiv(a, b, x, y), test: Eq[Bool, nat_lt(0, y), False_()]) -> IsGCD(a, b, x):
    y_zero = nat_lt_false_zero(y, test)
    self_common = transport[Nat, 0, y](lambda z: Common(x, x, z), sym(y_zero),
        Pair(divides_self(x), divides_zero(x)))
    return Pair(invariant(x).snd(self_common),
        lambda d: lambda proof: invariant(d).fst(proof).fst)
