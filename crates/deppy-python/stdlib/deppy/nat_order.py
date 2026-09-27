from deppy._builtins import inductive, constructor, Index, dependent, theorem, Nat, Z, S, Type, Pi, Eq, refl, absurd
from deppy.data import Empty, Unit, MkUnit, Sum, Left, Right, Decidable, Yes, No, sum_elim
from deppy.nat import add, add_comm, add_zero, pred_or, mul, mul_comm
from deppy.equality import cong, sym, transport


@inductive
class LE:
    r"""Evidence for :math:`n \le m`.

    ``left`` and ``right`` are the lower and upper natural-number indices.
    ``LEZero(m)`` proves :math:`0 \le m`; ``LESucc`` lifts a proof through
    successor on both sides.
    """
    left: Index[Nat]
    right: Index[Nat]

    @constructor
    def LEZero(n: Nat) -> LE[0, n]: ...
    @constructor
    def LESucc(n: Nat, m: Nat, step: LE[n, m]) -> LE[S(n), S(m)]: ...


@dependent
def LT(n: Nat, m: Nat) -> Type:
    r"""Strict order, defined by :math:`n < m \;\equiv\; n+1 \le m`."""
    return LE[S(n), m]


@dependent(decreases="n")
def le_refl(n: Nat) -> LE[n, n]:
    r"""Theorem ``le_refl``: :math:`n \le n`."""
    match n:
        case Z():
            return LEZero(0)
        case S(k):
            return LESucc(k, k, le_refl(k))


@dependent(decreases="p")
def le_step[n: Nat, m: Nat](p: LE[n, m]) -> LE[n, S(m)]:
    r"""Theorem ``le_step``: :math:`n \le m \Rightarrow n \le m+1`."""
    match p:
        case LEZero(k):
            return LEZero(S(k))
        case LESucc(a, b, q):
            return LESucc(a, S(b), le_step(q))


@dependent(decreases="p")
def le_pred(n: Nat, m: Nat, p: LE[S(n), S(m)]) -> LE[n, m]:
    r"""Cancel successor from both sides of an order proof."""
    match p:
        case LESucc(a, b, q):
            return q


@dependent(decreases="p")
def le_trans[n: Nat, m: Nat](p: LE[n, m], k: Nat, q: LE[m, k]) -> LE[n, k]:
    r"""Theorem ``le_trans``: :math:`n \le m \land m \le k \Rightarrow n \le k`."""
    match p:
        case LEZero(_):
            return LEZero(k)
        case LESucc(a, b, step):
            match q:
                case LESucc(j, end, proof):
                    return LESucc(a, end, le_trans(step, end, proof))


@theorem
def not_succ_le_zero(n: Nat, p: LE[S(n), 0]) -> Empty:
    r"""Theorem ``not_succ_le_zero``: :math:`\neg(n+1 \le 0)`."""
    return absurd(Empty, p)


@dependent(decreases="decision")
def le_decide_succ(n: Nat, m: Nat, decision: Decidable[LE[n, m]]) -> Decidable[LE[S(n), S(m)]]:
    r"""Lift a decision for :math:`n \le m` to one for :math:`n+1 \le m+1`."""
    match decision:
        case Yes(p):
            return Yes[LE[S(n), S(m)]](LESucc(n, m, p))
        case No(np):
            return No[LE[S(n), S(m)]](lambda p: np(le_pred(n, m, p)))


@dependent(decreases="m")
def le_decide_step(n: Nat, m: Nat, smaller: Pi[Nat, lambda b: Decidable[LE[n, b]]]) -> Decidable[LE[S(n), m]]:
    r"""Decide :math:`n+1 \le m` using decisions for :math:`n \le b`."""
    match m:
        case Z():
            return No[LE[S(n), 0]](lambda p: not_succ_le_zero(n, p))
        case S(b):
            return le_decide_succ(n, b, smaller(b))


@dependent(decreases="n")
def le_decide(n: Nat, m: Nat) -> Decidable[LE[n, m]]:
    r"""Compute a proof or refutation of :math:`n \le m`."""
    match n:
        case Z():
            return Yes[LE[0, m]](LEZero(m))
        case S(a):
            return le_decide_step(a, m, lambda b: le_decide(a, b))


@dependent
def lt_decide(n: Nat, m: Nat) -> Decidable[LT(n, m)]:
    r"""Compute a proof or refutation of :math:`n < m`."""
    return le_decide(S(n), m)


@theorem(decreases="m")
def le_total_succ(n: Nat, m: Nat, smaller: Pi[Nat, lambda b: Sum[LE[n, b], LE[b, n]]]) -> Sum[
    LE[S(n), m], LE[m, S(n)]
]:
    match m:
        case Z():
            return Right(LEZero(S(n)))
        case S(b):
            return sum_elim[LE[n, b], LE[b, n], Sum[LE[S(n), S(b)], LE[S(b), S(n)]]](
                smaller(b),
                lambda p: Left(LESucc(n, b, p)),
                lambda p: Right(LESucc(b, n, p)),
            )


@theorem(decreases="n")
def le_total(n: Nat, m: Nat) -> Sum[LE[n, m], LE[m, n]]:
    """Any two natural numbers are comparable."""
    match n:
        case Z():
            return Left(LEZero(m))
        case S(k):
            return le_total_succ(k, m, lambda b: le_total(k, b))


@theorem
def lt_to_succ_le(n: Nat, m: Nat, p: LT(n, m)) -> LE[S(n), m]:
    """Unfold strict order as successor-bounded non-strict order."""
    return p


@theorem
def succ_le_to_lt(n: Nat, m: Nat, p: LE[S(n), m]) -> LT(n, m):
    return p


@theorem
def lt_succ_to_le(n: Nat, m: Nat, p: LT(n, S(m))) -> LE[n, m]:
    return le_pred(n, m, p)


@theorem
def le_to_lt_succ(n: Nat, m: Nat, p: LE[n, m]) -> LT(n, S(m)):
    return LESucc(n, m, p)


@theorem(decreases="n")
def zero_le_lt_or_eq(n: Nat) -> Sum[LT(0, n), Eq[Nat, 0, n]]:
    match n:
        case Z():
            return Right(refl(0))
        case S(k):
            return Left(LESucc(0, k, LEZero(k)))


@theorem(decreases="p")
def le_lt_or_eq[n: Nat, m: Nat](p: LE[n, m]) -> Sum[LT(n, m), Eq[Nat, n, m]]:
    """A non-strict comparison is either strict or an equality."""
    match p:
        case LEZero(k):
            return zero_le_lt_or_eq(k)
        case LESucc(a, b, q):
            return sum_elim[LT(a, b), Eq[Nat, a, b], Sum[LT(S(a), S(b)), Eq[Nat, S(a), S(b)]]](
                le_lt_or_eq(q),
                lambda lt: Left(LESucc(S(a), b, lt)),
                lambda eq: Right(cong(lambda x: S(x), eq)),
            )


@theorem
def lt_succ_cases(n: Nat, m: Nat, p: LT(m, S(n))) -> Sum[LT(m, n), Eq[Nat, m, n]]:
    return le_lt_or_eq(le_pred(m, n, p))


@theorem(decreases="n")
def strong_induction_all[P: Pi[Nat, lambda _: Type]](
    n: Nat,
    step: Pi[Nat, lambda k: Pi[Pi[Nat, lambda m: Pi[LT(m, k), lambda _: P(m)]], lambda _: P(k)]],
) -> Pi[Nat, lambda m: Pi[LT(m, n), lambda _: P(m)]]:
    """Collect proofs for every value below a bound by ordinary induction."""
    match n:
        case Z():
            return lambda m: lambda smaller: absurd(P(m), not_succ_le_zero(m, smaller))
        case S(k):
            previous = strong_induction_all(k, step)
            current = step(k)(previous)
            return lambda m: lambda smaller: sum_elim[LT(m, k), Eq[Nat, m, k], P(m)](
                lt_succ_cases(k, m, smaller),
                lambda lt: previous(m)(lt),
                lambda eq: transport[Nat, k, m](P, sym(eq), current),
            )


@theorem
def strong_induction[P: Pi[Nat, lambda _: Type]](
    n: Nat,
    step: Pi[Nat, lambda k: Pi[Pi[Nat, lambda m: Pi[LT(m, k), lambda _: P(m)]], lambda _: P(k)]],
) -> P(n):
    """Prove P(n) assuming P(m) for every m strictly below each induction target."""
    return step(n)(strong_induction_all(n, step))


@theorem(decreases="n")
def lt_irrefl(n: Nat, p: LT(n, n)) -> Empty:
    r"""Theorem ``lt_irrefl``: :math:`\neg(n < n)`."""
    match n:
        case Z():
            return not_succ_le_zero(0, p)
        case S(k):
            return lt_irrefl(k, le_pred(S(k), k, p))


@theorem(decreases="p")
def le_weaken[n: Nat, m: Nat](p: LE[S(n), m]) -> LE[n, m]:
    r"""Theorem ``le_weaken``: :math:`n < m \Rightarrow n \le m`."""
    match p:
        case LESucc(a, b, q):
            return le_step(q)


@theorem
def lt_trans(n: Nat, m: Nat, k: Nat, p: LT(n, m), q: LT(m, k)) -> LT(n, k):
    r"""Theorem ``lt_trans``: :math:`n < m \land m < k \Rightarrow n < k`."""
    return le_trans(p, k, le_weaken(q))


@theorem(decreases="p")
def le_zero_eq[n: Nat](p: LE[n, 0]) -> Eq[Nat, n, 0]:
    r"""Theorem ``le_zero_eq``: :math:`n \le 0 \Rightarrow n = 0`."""
    match p:
        case LEZero(_):
            return refl(0)


@theorem(decreases="p")
def le_antisymm[n: Nat, m: Nat](p: LE[n, m], q: LE[m, n]) -> Eq[Nat, n, m]:
    r"""Theorem ``le_antisymm``: :math:`n \le m \land m \le n \Rightarrow n = m`."""
    match p:
        case LEZero(b):
            return sym(le_zero_eq(q))
        case LESucc(a, b, step):
            return cong[Nat, Nat](lambda k: S(k), le_antisymm(step, le_pred(b, a, q)))


@theorem(decreases="k")
def add_le_add_left(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[add(k, n), add(k, m)]:
    r"""Theorem ``add_le_add_left``: :math:`n \le m \Rightarrow k+n \le k+m`."""
    match k:
        case Z():
            return p
        case S(j):
            return LESucc(add(j, n), add(j, m), add_le_add_left(n, m, j, p))


@theorem(decreases="p")
def add_le_add_right[n: Nat, m: Nat](p: LE[n, m], k: Nat) -> LE[add(n, k), add(m, k)]:
    r"""Theorem ``add_le_add_right``: :math:`n \le m \Rightarrow n+k \le m+k`."""
    match p:
        case LEZero(b):
            prefix = transport[Nat, add(k, 0), k](lambda start: LE[start, add(k, b)], add_zero(k), add_le_add_left(0, b, k, LEZero(b)))
            return transport[Nat, add(k, b), add(b, k)](lambda end: LE[k, end], add_comm(k, b), prefix)
        case LESucc(a, b, q):
            return LESucc(add(a, k), add(b, k), add_le_add_right(q, k))


@theorem
def add_lt_add_right(n: Nat, m: Nat, k: Nat, p: LT(n, m)) -> LT(add(n, k), add(m, k)):
    r"""Theorem ``add_lt_add_right``: :math:`n < m \Rightarrow n+k < m+k`."""
    return add_le_add_right(p, k)


@theorem(decreases="k")
def mul_le_mul_right[n: Nat, m: Nat](p: LE[n, m], k: Nat) -> LE[mul(n, k), mul(m, k)]:
    """Multiplication on the right preserves natural-number order."""
    match k:
        case Z():
            return LEZero(0)
        case S(j):
            return le_trans(
                add_le_add_right(p, mul(n, j)),
                add(m, mul(m, j)),
                add_le_add_left(mul(n, j), mul(m, j), m, mul_le_mul_right(p, j)),
            )


@theorem
def mul_le_mul_left[n: Nat, m: Nat](k: Nat, p: LE[n, m]) -> LE[mul(k, n), mul(k, m)]:
    """Multiplication on the left preserves natural-number order."""
    lower = transport[Nat, mul(n, k), mul(k, n)](
        lambda x: LE[x, mul(m, k)], mul_comm(n, k), mul_le_mul_right(p, k)
    )
    return transport[Nat, mul(m, k), mul(k, m)](
        lambda x: LE[mul(k, n), x], mul_comm(m, k), lower
    )


@theorem
def mul_lt_succ(k: Nat, n: Nat, positive: LT(0, k)) -> LT(mul(k, n), mul(k, S(n))):
    """A positive multiplier makes the next product strictly larger."""
    return add_le_add_right(positive, mul(k, n))


@theorem(decreases="p")
def mul_lt_mul_left(k: Nat, n: Nat, m: Nat, positive: LT(0, k), p: LT(n, m)) -> LT(mul(k, n), mul(k, m)):
    """Multiplication by a positive number preserves strict order."""
    match p:
        case LESucc(a, b, q):
            return le_trans(
                mul_lt_succ(k, a, positive),
                mul(k, S(b)),
                mul_le_mul_left(k, LESucc(a, b, q)),
            )


@theorem
def mul_lt_eq_absurd(k: Nat, n: Nat, m: Nat, positive: LT(0, k), smaller: LT(n, m),
                     equal: Eq[Nat, mul(k, n), mul(k, m)]) -> Empty:
    contradiction = transport[Nat, mul(k, m), mul(k, n)](
        lambda x: LT(mul(k, n), x), sym(equal), mul_lt_mul_left(k, n, m, positive, smaller)
    )
    return lt_irrefl(mul(k, n), contradiction)


@theorem
def mul_left_cancel_pos(k: Nat, n: Nat, m: Nat, positive: LT(0, k),
                        equal: Eq[Nat, mul(k, n), mul(k, m)]) -> Eq[Nat, n, m]:
    """Cancel a positive left multiplier from an equality."""
    return sum_elim[LE[n, m], LE[m, n], Eq[Nat, n, m]](
        le_total(n, m),
        lambda forward: sum_elim[LT(n, m), Eq[Nat, n, m], Eq[Nat, n, m]](
            le_lt_or_eq(forward),
            lambda strict: absurd(Eq[Nat, n, m], mul_lt_eq_absurd(k, n, m, positive, strict, equal)),
            lambda same: same,
        ),
        lambda backward: sum_elim[LT(m, n), Eq[Nat, m, n], Eq[Nat, n, m]](
            le_lt_or_eq(backward),
            lambda strict: absurd(Eq[Nat, n, m], mul_lt_eq_absurd(k, m, n, positive, strict, sym(equal))),
            lambda same: sym(same),
        ),
    )


@theorem(decreases="n")
def pred_lt(n: Nat, positive: LT(0, n)) -> LT(pred_or(0, n), n):
    r"""Theorem ``pred_lt``: :math:`0 < n \Rightarrow \operatorname{pred}(n) < n`."""
    match n:
        case Z():
            return absurd(LT(pred_or(0, 0), 0), positive)
        case S(k):
            return le_refl(S(k))
