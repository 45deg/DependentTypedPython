from deppy._builtins import dependent, theorem, Nat, Z, S, Eq, refl, Sigma, Pair, Pi, absurd
from deppy.nat import add, mul, pred_or, add_zero, add_comm, add_succ
from deppy.nat_order import LE, LT, LEZero, LESucc, pred_lt, le_trans, le_weaken, le_refl, le_decide, lt_decide
from deppy.equality import cong, sym, trans, transport
from deppy.data import Bool, True_, False_, Empty
from deppy.bool import select, decision_true_intro, false_ne_true, select_post_eq, bool_not
from deppy.nat_bool import nat_eq, nat_le, nat_lt, nat_lt_true, is_zero, equal_step, equal, zero_equal, step_equal, equal_true, equal_refl, equal_false


@dependent(decreases="m")
def sub_count(m: Nat, n: Nat) -> Nat:
    """Total truncated subtraction. Verified `-` additionally requires m <= n."""
    match m:
        case Z():
            return n
        case S(k):
            return sub_count(k, pred_or(0, n))


@dependent
def sub(n: Nat, m: Nat) -> Nat:
    """Truncated natural subtraction."""
    return sub_count(m, n)


@theorem(decreases="p")
def sub_add[m: Nat, n: Nat](p: LE[m, n]) -> Eq[Nat, add(m, sub(n, m)), n]:
    """Under the checked lower bound, subtraction is inverse to addition."""
    match p:
        case LEZero(k):
            return refl(k)
        case LESucc(a, b, rest):
            return cong(lambda x: S(x), sub_add(rest))








@dependent
def divmod_step(d: Nat, qr: Sigma[Nat, lambda _: Nat]) -> Sigma[Nat, lambda _: Nat]:
    return select[Sigma[Nat, lambda _: Nat]](equal(S(qr.snd), d), Pair(qr.fst, S(qr.snd)), Pair(S(qr.fst), 0))


@dependent(decreases="n")
def divmod(n: Nat, d: Nat) -> Sigma[Nat, lambda _: Nat]:
    """Unary division. The frontend requires d > 0 for // and %."""
    match n:
        case Z():
            return Pair(0, 0)
        case S(k):
            return divmod_step(d, divmod(k, d))


@dependent
def quotient(n: Nat, d: Nat) -> Nat:
    """Return the quotient of unary division."""
    return divmod(n, d).fst


@dependent
def remainder(n: Nat, d: Nat) -> Nat:
    """Return the remainder of unary division."""
    return divmod(n, d).snd


@theorem
def sub_bound(n: Nat, m: Nat, proof: LE[m, n]) -> Eq[Bool, nat_le(m, n), True_()]:
    return decision_true_intro(le_decide(m, n), proof)


@theorem(decreases="n")
def pred_le(n: Nat) -> LE[pred_or(0, n), n]:
    match n:
        case Z():
            return LEZero(0)
        case S(k):
            return le_weaken(pred_lt(S(k), LESucc(0, k, LEZero(k))))


@theorem(decreases="m")
def sub_le(m: Nat, n: Nat) -> LE[sub(n, m), n]:
    match m:
        case Z():
            return le_refl(n)
        case S(k):
            return le_trans(sub_le(k, pred_or(0, n)), n, pred_le(n))












@theorem
def zero_strict(m: Nat, different: Pi[Eq[Nat, 0, m], lambda _: Empty]) -> LT(0, m):
    match m:
        case Z():
            return absurd(LT(0, 0), different(refl(0)))
        case S(k):
            return LESucc(0, k, LEZero(k))


@theorem(decreases="bound")
def le_strict[n: Nat, m: Nat](bound: LE[n, m], different: Pi[Eq[Nat, n, m], lambda _: Empty]) -> LT(n, m):
    match bound:
        case LEZero(k):
            return zero_strict(k, different)
        case LESucc(a, b, p):
            return LESucc(S(a), b, le_strict(p, lambda same: different(cong(lambda x: S(x), same))))


@theorem
def divmod_step_bound(d: Nat, qr: Sigma[Nat, lambda _: Nat], positive: LT(0, d), bound: LT(qr.snd, d)) -> LT(divmod_step(d, qr).snd, d):
    return select_post_eq[Sigma[Nat, lambda _: Nat], lambda result: LT(result.snd, d)](equal(S(qr.snd), d), Pair(qr.fst, S(qr.snd)), Pair(S(qr.fst), 0), lambda test: le_strict(bound, lambda same: equal_false(S(qr.snd), d, test, same)), lambda test: positive)


@theorem(decreases="n")
def divmod_bound(n: Nat, d: Nat, positive: LT(0, d)) -> LT(divmod(n, d).snd, d):
    """The remainder is smaller than a positive divisor."""
    match n:
        case Z():
            return positive
        case S(k):
            return divmod_step_bound(d, divmod(k, d), positive, divmod_bound(k, d, positive))


@theorem
def remainder_lt_true(n: Nat, d: Nat, test: Eq[Bool, nat_lt(0, d), True_()]) -> LT(remainder(n, d), d):
    """A true positive-divisor guard bounds the remainder."""
    return divmod_bound(n, d, nat_lt_true(0, d, test))


@theorem
def divmod_wrap(d: Nat, q: Nat, r: Nat, same: Eq[Nat, S(r), d]) -> Eq[Nat, add(mul(d, S(q)), 0), S(add(mul(d, q), r))]:
    return trans(add_zero(add(d, mul(d, q))), trans(add_comm(d, mul(d, q)), trans(cong(lambda x: add(mul(d, q), x), sym(same)), add_succ(mul(d, q), r))))


@theorem
def divmod_step_equation(n: Nat, d: Nat, qr: Sigma[Nat, lambda _: Nat], equation: Eq[Nat, add(mul(d, qr.fst), qr.snd), n]) -> Eq[Nat, add(mul(d, divmod_step(d, qr).fst), divmod_step(d, qr).snd), S(n)]:
    return select_post_eq[Sigma[Nat, lambda _: Nat], lambda result: Eq[Nat, add(mul(d, result.fst), result.snd), S(n)]](equal(S(qr.snd), d), Pair(qr.fst, S(qr.snd)), Pair(S(qr.fst), 0), lambda test: trans(add_succ(mul(d, qr.fst), qr.snd), cong(lambda x: S(x), equation)), lambda test: trans(divmod_wrap(d, qr.fst, qr.snd, equal_true(S(qr.snd), d, test)), cong(lambda x: S(x), equation)))


@theorem(decreases="n")
def divmod_equation(n: Nat, d: Nat) -> Eq[Nat, add(mul(d, quotient(n, d)), remainder(n, d)), n]:
    """Quotient and remainder reconstruct the dividend."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return divmod_step_equation(k, d, divmod(k, d), divmod_equation(k, d))


@theorem
def divisor_positive(d: Nat, proof: LT(0, d)) -> Eq[Bool, nat_lt(0, d), True_()]:
    return decision_true_intro(lt_decide(0, d), proof)


@theorem
def nonzero_positive(d: Nat, test: Eq[Bool, bool_not(nat_eq(d, 0)), True_()]) -> Eq[Bool, nat_lt(0, d), True_()]:
    match d:
        case Z():
            return absurd(Eq[Bool, nat_lt(0, 0), True_()], false_ne_true(test))
        case S(k):
            return refl(True_())


@theorem
def unequal_zero_positive(d: Nat, test: Eq[Bool, nat_eq(d, 0), False_()]) -> Eq[Bool, nat_lt(0, d), True_()]:
    match d:
        case Z():
            return absurd(Eq[Bool, nat_lt(0, 0), True_()], false_ne_true(sym(test)))
        case S(k):
            return refl(True_())
