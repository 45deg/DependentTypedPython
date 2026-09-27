from deppy._builtins import dependent, theorem, Nat, Z, S, Type, Pi, Eq, refl, absurd
from deppy.equality import cong, sym, trans, transport
from deppy.data import Bool, False_, True_, Empty
from deppy.bool import decision_bool, decision_true, decision_true_intro, select, bool_not, not_false, and_left, and_right, false_ne_true
from deppy.nat import pred_or
from deppy.nat_order import pred_lt, LE, LT, le_decide, lt_decide, le_trans, le_weaken, le_antisymm, le_refl


@dependent
def nat_le(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n \le m` for a verified branch condition."""
    return decision_bool(le_decide(n, m))


@dependent
def nat_lt(n: Nat, m: Nat) -> Bool:
    r"""Compute whether :math:`n < m` for a verified branch condition."""
    return decision_bool(lt_decide(n, m))


@theorem
def nat_lt_true(n: Nat, m: Nat, test: Eq[Bool, nat_lt(n, m), True_()]) -> LT(n, m):
    """Recover strict order evidence from a verified guard."""
    return decision_true(lt_decide(n, m), test)


@theorem
def nat_le_true(n: Nat, m: Nat, test: Eq[Bool, nat_le(n, m), True_()]) -> LE[n, m]:
    """Recover non-strict order evidence from a verified guard."""
    return decision_true(le_decide(n, m), test)


@theorem(decreases="n")
def nat_lt_false_zero(n: Nat, test: Eq[Bool, nat_lt(0, n), False_()]) -> Eq[Nat, n, 0]:
    """A natural number that is not positive is zero."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@theorem
def lt_le_bound[n: Nat, m: Nat](smaller: LT(n, m), k: Nat, bound: LE[m, k]) -> LE[n, k]:
    """A strict decrease preserves an existing upper bound."""
    return le_trans(le_weaken(smaller), k, bound)


@theorem
def pred_lt_true(n: Nat, test: Eq[Bool, nat_lt(0, n), True_()]) -> LT(pred_or(0, n), n):
    """A positive loop guard justifies decrementing the counter."""
    return pred_lt(n, nat_lt_true(0, n, test))


@dependent
def nat_eq(left: Nat, right: Nat) -> Bool:
    """Compare natural numbers using checked order decisions."""
    return select[Bool](nat_le(left, right), False_(), nat_le(right, left))


@theorem
def nat_lt_not_false(n: Nat, m: Nat, proof: Eq[Bool, bool_not(nat_lt(n, m)), False_()]) -> LT(n, m):
    """Recover strict order on the false branch of a negated guard."""
    return nat_lt_true(n, m, not_false(nat_lt(n, m), proof))


@theorem
def nat_eq_true(n: Nat, m: Nat, proof: Eq[Bool, nat_eq(n, m), True_()]) -> Eq[Nat, n, m]:
    """Recover propositional equality from a true equality guard."""
    return le_antisymm(nat_le_true(n, m, and_left(nat_le(n, m), nat_le(m, n), proof)), nat_le_true(m, n, and_right(nat_le(n, m), nat_le(m, n), proof)))


@theorem
def nat_le_refl_true(n: Nat) -> Eq[Bool, nat_le(n, n), True_()]:
    """The non-strict comparison of a natural number with itself is true."""
    return decision_true_intro(le_decide(n, n), le_refl(n))


@dependent
def is_zero(m: Nat) -> Bool:
    """Return true exactly for zero."""
    match m:
        case Z():
            return True_()
        case S(k):
            return False_()


@dependent
def equal_step(m: Nat, smaller: Pi[Nat, lambda _: Bool]) -> Bool:
    """Compare a successor with the second argument using a smaller comparison."""
    match m:
        case Z():
            return False_()
        case S(k):
            return smaller(k)


@dependent(decreases="n")
def equal(n: Nat, m: Nat) -> Bool:
    """Compare naturals by structural recursion."""
    match n:
        case Z():
            return is_zero(m)
        case S(k):
            return equal_step(m, lambda j: equal(k, j))


@theorem
def zero_equal(m: Nat, proof: Eq[Bool, is_zero(m), True_()]) -> Eq[Nat, 0, m]:
    """Reflect a true zero test into natural equality."""
    match m:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, 0, S(k)], false_ne_true(proof))


@theorem
def step_equal(n: Nat, m: Nat, ih: Pi[Nat, lambda j: Pi[Eq[Bool, equal(n, j), True_()], lambda _: Eq[Nat, n, j]]], proof: Eq[Bool, equal_step(m, lambda j: equal(n, j)), True_()]) -> Eq[Nat, S(n), m]:
    """Reflect a true successor comparison using the smaller reflection proof."""
    match m:
        case Z():
            return absurd(Eq[Nat, S(n), 0], false_ne_true(proof))
        case S(k):
            return cong(lambda x: S(x), ih(k)(proof))


@theorem(decreases="n")
def equal_true(n: Nat, m: Nat, proof: Eq[Bool, equal(n, m), True_()]) -> Eq[Nat, n, m]:
    """A true structural equality test yields propositional equality."""
    match n:
        case Z():
            return zero_equal(m, proof)
        case S(k):
            return step_equal(k, m, lambda j, p: equal_true(k, j, p), proof)


@theorem(decreases="n")
def equal_refl(n: Nat) -> Eq[Bool, equal(n, n), True_()]:
    """Structural equality returns true on equal inputs."""
    match n:
        case Z():
            return refl(True_())
        case S(k):
            return equal_refl(k)


@theorem
def equal_false(n: Nat, m: Nat, proof: Eq[Bool, equal(n, m), False_()], same: Eq[Nat, n, m]) -> Empty:
    """A false structural equality test refutes propositional equality."""
    return false_ne_true(trans(sym(proof), transport[Nat, n, m](lambda j: Eq[Bool, equal(n, j), True_()], same, equal_refl(n))))


@theorem
def nat_eq_refl_true(n: Nat) -> Eq[Bool, nat_eq(n, n), True_()]:
    """The order based equality test accepts equal inputs."""
    return trans(
        cong(lambda b: select[Bool](b, False_(), nat_le(n, n)), nat_le_refl_true(n)),
        nat_le_refl_true(n),
    )


@theorem
def nat_eq_intro(n: Nat, m: Nat, same: Eq[Nat, n, m]) -> Eq[Bool, nat_eq(n, m), True_()]:
    return transport[Nat, n, m](lambda j: Eq[Bool, nat_eq(n, j), True_()], same, nat_eq_refl_true(n))


@theorem
def equal_intro(n: Nat, m: Nat, same: Eq[Nat, n, m]) -> Eq[Bool, equal(n, m), True_()]:
    return transport[Nat, n, m](lambda j: Eq[Bool, equal(n, j), True_()], same, equal_refl(n))


@theorem(decreases="a")
def same_boolean_from_true(
    a: Bool, b: Bool,
    forward: Pi[Eq[Bool, a, True_()], lambda _: Eq[Bool, b, True_()]],
    backward: Pi[Eq[Bool, b, True_()], lambda _: Eq[Bool, a, True_()]],
) -> Eq[Bool, a, b]:
    match a:
        case False_():
            match b:
                case False_():
                    return refl(False_())
                case True_():
                    return absurd(Eq[Bool, False_(), True_()], false_ne_true(backward(refl(True_()))))
        case True_():
            match b:
                case False_():
                    return absurd(Eq[Bool, True_(), False_()], false_ne_true(forward(refl(True_()))))
                case True_():
                    return refl(True_())


@theorem
def equal_nat_eq(n: Nat, m: Nat) -> Eq[Bool, equal(n, m), nat_eq(n, m)]:
    """The structural and order based equality tests agree on every pair."""
    return same_boolean_from_true(
        equal(n, m), nat_eq(n, m),
        lambda proof: nat_eq_intro(n, m, equal_true(n, m, proof)),
        lambda proof: equal_intro(n, m, nat_eq_true(n, m, proof)),
    )
