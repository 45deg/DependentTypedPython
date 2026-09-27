from deppy import (
    dependent,
    theorem,
    record,
    Type,
    Pi,
    Sigma,
    Pair,
    Nat,
    S,
    Eq,
    refl,
    absurd,
    nat_elim,
)
from deppy.equality import sym, trans, cong, transport
from deppy.nat import add, mul, add_succ
from deppy.lists import count_split
from deppy.nat_order import LE, LEZero, LESucc, le_refl, le_step, le_pred, le_trans
from common import (
    B0,
    B1,
    Bit,
    Cons,
    Decision,
    Enumeration,
    Group,
    Has,
    IsZero,
    Left,
    List,
    Nil,
    No,
    Not,
    Right,
    Subgroup,
    Unit,
    Unit_,
    Yes,
    bijection_count,
    bit_enumeration,
    bit_group,
    count,
    count_map,
    decision_weight,
    either_elim,
    left_recover,
    length,
    reject,
    reject_head,
    right_recover,
    weight_no,
    weight_transport,
    xor,
)

# A constructive proof using the shared definitions in common.py. No axioms or unchecked assertions.
# Finite enumerations contain each carrier element exactly once. Membership of
# the subgroup is decidable; no quotient type or choice principle is used.
# Check with: cargo run -p deppy-python --locked --offline -- \
#     crates/deppy-python/examples/proof_case/lagrange.py
# Opaque lemmas have checked bodies; opacity only prevents their unfolding.


@dependent
def Related[A: Type](g: Group[A], h: Subgroup[A, g], a: A, b: A) -> Type:
    r"""Express equality of left cosets by membership of a inverse times b in H."""
    return h.member(g.op(g.inverse(a))(b))


@theorem
def related_refl[A: Type](g: Group[A], h: Subgroup[A, g], a: A) -> Related(g, h, a, a):
    r"""Prove coset reflexivity from inverse cancellation and identity membership."""
    return transport[A, g.unit, g.op(g.inverse(a))(a)](
        h.member, sym(g.left_inverse(a)), h.unit_closed
    )


@theorem
def related_witness[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A, x: A, px: h.member(x), eq: Eq[A, g.op(a)(x), b]
) -> Related(g, h, a, b):
    r"""A factorization b = a*x with x in H places b in the coset of a.

    Cancel a and transport the supplied subgroup membership proof.
    """
    return transport[A, x, g.op(g.inverse(a))(b)](
        h.member, trans(sym(left_recover(g, a, x)), cong(lambda y: g.op(g.inverse(a))(y), eq)), px
    )


@theorem
def cancel_right_inverse[A: Type](
    g: Group[A], a: A, x: A
) -> Eq[A, g.op(g.op(a)(x))(g.inverse(x)), a]:
    r"""Simplify (a*x)*inverse(x) to a by associativity and inverse cancellation."""
    return trans(
        g.assoc(a)(x)(g.inverse(x)),
        trans(cong(lambda y: g.op(a)(y), g.right_inverse(x)), g.right_unit(a)),
    )


@theorem
def related_sym[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A, p: Related(g, h, a, b)
) -> Related(g, h, b, a):
    r"""Reverse a coset relation using closure under inverses.

    The inverse of the original subgroup witness supplies the reverse factorization.
    """
    x = g.op(g.inverse(a))(b)
    return related_witness(
        g,
        h,
        b,
        a,
        g.inverse(x),
        h.inv_closed(x)(p),
        trans(
            cong(lambda y: g.op(y)(g.inverse(x)), sym(right_recover(g, a, b))),
            cancel_right_inverse(g, a, x),
        ),
    )


@theorem
def related_trans[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A, c: A, p: Related(g, h, a, b), q: Related(g, h, b, c)
) -> Related(g, h, a, c):
    r"""Compose coset relations by multiplying their subgroup witnesses.

    Closure under multiplication and cancellation give the composite factorization.
    """
    x = g.op(g.inverse(a))(b)
    y = g.op(g.inverse(b))(c)
    return related_witness(
        g,
        h,
        a,
        c,
        g.op(x)(y),
        h.mul_closed(x)(y)(p)(q),
        trans(
            sym(g.assoc(a)(x)(y)),
            trans(cong(lambda z: g.op(z)(y), right_recover(g, a, b)), right_recover(g, b, c)),
        ),
    )


@theorem
def fiber_count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]],
    f: Pi[A, lambda _: A],
    back: Pi[A, lambda _: A],
    left_inverse: Pi[A, lambda x: Eq[A, back(f(x)), x]],
    right_inverse: Pi[A, lambda x: Eq[A, f(back(x)), x]],
    finite: Enumeration[A],
) -> Eq[
    Nat,
    count[A, lambda x: P(back(x))](lambda x: dec(back(x)), finite.elements),
    count(dec, finite.elements),
]:
    r"""A bijection preserves the count of a predicate pulled back along its inverse.

    Combine enumeration invariance with equality of the pointwise decision weights.
    """
    return trans(
        sym(
            bijection_count[A, lambda x: P(back(x))](
                lambda x: dec(back(x)), f, back, left_inverse, right_inverse, finite
            )
        ),
        count_map[A, A, lambda x: P(back(x)), P](
            lambda x: dec(back(x)),
            dec,
            f,
            lambda x: weight_transport[A, P, back(f(x)), x](
                left_inverse(x), dec(back(f(x))), dec(x)
            ),
            finite.elements,
        ),
    )


@theorem
def coset_size[A: Type](
    g: Group[A], h: Subgroup[A, g], finite: Enumeration[A], a: A
) -> Eq[
    Nat,
    count[A, lambda x: Related(g, h, a, x)](
        lambda x: h.decide(g.op(g.inverse(a))(x)), finite.elements
    ),
    count(h.decide, finite.elements),
]:
    r"""Every left coset has the same cardinality as the subgroup.

    Left multiplication and multiplication by its inverse give the required bijection.
    """
    return fiber_count[A, h.member](
        h.decide,
        lambda x: g.op(a)(x),
        lambda x: g.op(g.inverse(a))(x),
        lambda x: left_recover(g, a, x),
        lambda x: right_recover(g, a, x),
        finite,
    )


# Removing one complete equivalence class decreases the finite search bound.
@theorem(decreases="d")
def reject_bound_head[A: Type, P: Type](
    x: A, d: Decision[P], tail: List[A], n: Nat, bound: LE[length(tail), n]
) -> LE[length(reject_head(x, d, tail)), S(n)]:
    r"""Filtering one head increases the tail length bound by at most one.

    Split on whether the head is discarded or retained.
    """
    match d:
        case Yes(p):
            return le_step(bound)
        case No(np):
            return LESucc(length(tail), n, bound)


@theorem(decreases="xs")
def reject_bound[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> LE[length(reject(dec, xs)), length(xs)]:
    r"""Filtering cannot increase list length.

    Induct on the list using the bound for one filtered head.
    """
    match xs:
        case Nil():
            return LEZero(0)
        case Cons(x, tail):
            return reject_bound_head(
                x, dec(x), reject(dec, tail), length(tail), reject_bound(dec, tail)
            )


@theorem(decreases="d")
def reject_head_yes[A: Type, P: Type](
    x: A, d: Decision[P], rest: List[A], proof: P
) -> Eq[List[A], reject_head(x, d, rest), rest]:
    r"""A proved predicate forces filtering to discard the head.

    A negative decision contradicts the supplied proof.
    """
    match d:
        case Yes(p):
            return refl(rest)
        case No(np):
            return absurd(Eq[List[A], Cons(x, rest), rest], np(proof))


@theorem(decreases="dq")
def disjoint_head[A: Type, P: Pi[A, lambda _: Type], Q: Type](
    dp: Pi[A, lambda x: Decision[P(x)]],
    x: A,
    dq: Decision[Q],
    rest: List[A],
    disjoint: Pi[P(x), lambda _: Not(Q)],
) -> Eq[Nat, count(dp, reject_head(x, dq, rest)), add(decision_weight(dp(x)), count(dp, rest))]:
    r"""Discarding a head satisfying Q preserves the P-count when P excludes Q.

    In the discarded case its P-weight is zero.
    """
    match dq:
        case Yes(q):
            return sym(
                cong(lambda n: add(n, count(dp, rest)), weight_no(dp(x), lambda p: disjoint(p)(q)))
            )
        case No(nq):
            return refl(add(decision_weight(dp(x)), count(dp, rest)))


@theorem(decreases="xs")
def disjoint_count[A: Type, P: Pi[A, lambda _: Type], Q: Pi[A, lambda _: Type]](
    dp: Pi[A, lambda x: Decision[P(x)]],
    dq: Pi[A, lambda x: Decision[Q(x)]],
    disjoint: Pi[A, lambda x: Pi[P(x), lambda _: Not(Q(x))]],
    xs: List[A],
) -> Eq[Nat, count(dp, reject(dq, xs)), count(dp, xs)]:
    r"""Removing entries satisfying Q preserves the count of a disjoint predicate P.

    Induct on the list and use the one-head disjointness result.
    """
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(
                disjoint_head(dp, x, dq(x), reject(dq, tail), disjoint(x)),
                cong(
                    lambda n: add(decision_weight(dp(x)), n), disjoint_count(dp, dq, disjoint, tail)
                ),
            )


@theorem(decreases="d")
def reject_info_head[A: Type, P: Pi[A, lambda _: Type]](
    x: A,
    y: A,
    d: Decision[P(y)],
    tail: List[A],
    rest: List[A],
    info: Pi[Has(x, rest), lambda _: Sigma[Has(x, tail), lambda _: Not(P(x))]],
    member: Has(x, reject_head(y, d, rest)),
) -> Sigma[Has(x, Cons(y, tail)), lambda _: Not(P(x))]:
    r"""Recover original membership and predicate failure after filtering a head.

    Split the decision and transport the refutation when membership is at the head.
    """
    match d:
        case Yes(p):
            return Pair(Right(info(member).fst), info(member).snd)
        case No(np):
            return either_elim[
                Eq[A, x, y], Has(x, rest), Sigma[Has(x, Cons(y, tail)), lambda _: Not(P(x))]
            ](
                member,
                lambda eq: Pair(Left(eq), lambda px: np(transport[A, x, y](P, eq, px))),
                lambda later: Pair(Right(info(later).fst), info(later).snd),
            )


@theorem(decreases="xs")
def reject_info[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], x: A, xs: List[A], member: Has(x, reject(dec, xs))
) -> Sigma[Has(x, xs), lambda _: Not(P(x))]:
    r"""A retained entry belonged to the original list and fails the predicate.

    Induct on the source list, following the retained membership proof.
    """
    match xs:
        case Nil():
            return absurd(Sigma[Has(x, Nil[A]()), lambda _: Not(P(x))], member)
        case Cons(y, tail):
            return reject_info_head[A, P](
                x,
                y,
                dec(y),
                tail,
                reject(dec, tail),
                lambda later: reject_info(dec, x, tail, later),
                member,
            )


@record
class Equivalence[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]]:
    r"""Proof that ``R`` is an equivalence relation.

    :ivar reflexive: Evidence of :math:`R(a,a)`.
    :ivar symmetric: A map from :math:`R(a,b)` to :math:`R(b,a)`.
    :ivar transitive: A map from :math:`R(a,b)` and :math:`R(b,c)` to :math:`R(a,c)`.
    """
    reflexive: Pi[A, lambda a: R(a)(a)]
    symmetric: Pi[A, lambda a: Pi[A, lambda b: Pi[R(a)(b), lambda _: R(b)(a)]]]
    transitive: Pi[
        A,
        lambda a: Pi[
            A, lambda b: Pi[A, lambda c: Pi[R(a)(b), lambda p: Pi[R(b)(c), lambda q: R(a)(c)]]]
        ],
    ]


@dependent
def class_size[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]], a: A, xs: List[A]
) -> Nat:
    r"""Count occurrences related to a representative within the supplied list."""
    return count[A, R(a)](dec(a), xs)


@dependent
def Uniform[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]], h: Nat, xs: List[A]
) -> Type:
    r"""Require every represented equivalence class to have the common size h."""
    return Pi[A, lambda a: Pi[Has(a, xs), lambda _: Eq[Nat, class_size(dec, a, xs), h]]]


@dependent
def Divisible(h: Nat, n: Nat) -> Type:
    # The witness is an actual natural number, together with its equality proof.
    r"""Witness divisibility with a natural k and a proof that n = h*k."""
    return Sigma[Nat, lambda k: Eq[Nat, n, mul(h, k)]]


@theorem
def class_disjoint[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    laws: Equivalence[A, R], a: A, b: A, distinct: Not(R(a)(b)), x: A, p: R(b)(x)
) -> Not(R(a)(x)):
    r"""Classes of unrelated representatives cannot intersect.

    An intersection would relate the representatives by symmetry and transitivity.
    """
    return lambda q: distinct(laws.transitive(a)(x)(b)(q)(laws.symmetric(b)(x)(p)))


@theorem
def uniform_remainder[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    a: A,
    tail: List[A],
    uniform: Uniform(dec, h, Cons(a, tail)),
    b: A,
    member: Has(b, reject(dec(a), tail)),
) -> Eq[Nat, class_size(dec, b, reject(dec(a), tail)), h]:
    r"""Removing one class preserves the common size of all remaining classes.

    Disjointness preserves their counts, and the removed head contributes zero.
    """
    info = reject_info(dec(a), b, tail, member)
    unchanged = disjoint_count[A, R(b), R(a)](
        dec(b), dec(a), lambda x: lambda p: class_disjoint(laws, a, b, info.snd, x, p), tail
    )
    missing = weight_no(dec(b)(a), lambda p: info.snd(laws.symmetric(b)(a)(p)))
    return trans(
        unchanged,
        trans(
            sym(cong(lambda n: add(n, class_size(dec, b, tail)), missing)),
            uniform(b)(Right(info.fst)),
        ),
    )


@theorem
def split_selected[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    a: A,
    tail: List[A],
) -> Eq[
    Nat, length(Cons(a, tail)), add(class_size(dec, a, Cons(a, tail)), length(reject(dec(a), tail)))
]:
    r"""Split a nonempty list into the head's class and its complement.

    Reflexivity ensures the head itself is removed from the complement.
    """
    return trans(
        sym(count_split(dec(a), Cons(a, tail))),
        cong[List[A], Nat](
            lambda xs: add(class_size(dec, a, Cons(a, tail)), length(xs)),
            reject_head_yes(a, dec(a)(a), reject(dec(a), tail), laws.reflexive(a)),
        ),
    )


@dependent
def PartitionAt[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]], h: Nat, fuel: Nat
) -> Type:
    r"""State divisibility for uniform lists whose length is bounded by fuel."""
    return Pi[
        List[A],
        lambda xs: Pi[
            LE[length(xs), fuel],
            lambda bound: Pi[Uniform(dec, h, xs), lambda uniform: Divisible(h, length(xs))],
        ],
    ]


@theorem(decreases="xs")
def partition_zero[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    h: Nat,
    xs: List[A],
    bound: LE[length(xs), 0],
) -> Divisible(h, length(xs)):
    r"""A list bounded in length by zero has divisibility witness zero.

    The nonempty case contradicts the length bound.
    """
    match xs:
        case Nil():
            return Pair(0, refl(0))
        case Cons(x, tail):
            return absurd(Divisible(h, S(length(tail))), bound)


@theorem
def partition_step[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    fuel: Nat,
    ih: PartitionAt(dec, h, fuel),
    a: A,
    tail: List[A],
    bound: LE[S(length(tail)), S(fuel)],
    uniform: Uniform(dec, h, Cons(a, tail)),
) -> Divisible(h, S(length(tail))):
    r"""Remove the head's class and increment the remainder's divisibility witness.

    Filtering gives a smaller bound; uniformity fixes the removed count at h.
    """
    rest = reject(dec(a), tail)
    smaller = le_trans(reject_bound(dec(a), tail), fuel, le_pred(length(tail), fuel, bound))
    result = ih(rest)(smaller)(
        lambda b: lambda member: uniform_remainder(dec, laws, h, a, tail, uniform, b, member)
    )
    selected = uniform(a)(Left(refl(a)))
    proof = trans(
        split_selected(dec, laws, a, tail),
        trans(
            cong(lambda n: add(n, length(rest)), selected), cong(lambda n: add(h, n), result.snd)
        ),
    )
    return Pair(S(result.fst), proof)


@theorem(decreases="xs")
def partition_succ[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    fuel: Nat,
    ih: PartitionAt(dec, h, fuel),
    xs: List[A],
    bound: LE[length(xs), S(fuel)],
    uniform: Uniform(dec, h, xs),
) -> Divisible(h, length(xs)):
    r"""Handle a successor fuel bound by splitting the empty and nonempty cases.

    The nonempty case removes one class before applying the induction hypothesis.
    """
    match xs:
        case Nil():
            return Pair(0, refl(0))
        case Cons(a, tail):
            return partition_step(dec, laws, h, fuel, ih, a, tail, bound, uniform)


@theorem
def partition_fuel[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    fuel: Nat,
) -> PartitionAt(dec, h, fuel):
    r"""Prove uniform partition divisibility by induction on the length bound.

    Explicit fuel accommodates recursion on a filtered remainder.
    """
    return nat_elim(
        0,
        lambda n: PartitionAt(dec, h, n),
        lambda xs: lambda bound: lambda uniform: partition_zero(dec, h, xs, bound),
        lambda n, ih: (
            lambda xs: (
                lambda bound: (
                    lambda uniform: partition_succ(dec, laws, h, n, ih, xs, bound, uniform)
                )
            )
        ),
        fuel,
    )


@theorem
def uniform_partition[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    xs: List[A],
    uniform: Uniform(dec, h, xs),
) -> Divisible(h, length(xs)):
    r"""A uniform finite list has length divisible by its common class size.

    Instantiate the fuel induction with the list's own length.
    """
    return partition_fuel(dec, laws, h, length(xs))(xs)(le_refl(length(xs)))(uniform)


# Every hypothesis below is group structure, a decidable subgroup, or an
# exhaustive duplicate-free enumeration. No coset partition is supplied.
@theorem
def coset_equivalence[A: Type](
    g: Group[A], h: Subgroup[A, g]
) -> Equivalence[A, lambda a: lambda b: Related(g, h, a, b)]:
    r"""Package reflexivity, symmetry, and transitivity of the coset relation."""
    return Equivalence[A, lambda a: lambda b: Related(g, h, a, b)](
        lambda a: related_refl(g, h, a),
        lambda a: lambda b: lambda p: related_sym(g, h, a, b, p),
        lambda a: lambda b: lambda c: lambda p: lambda q: related_trans(g, h, a, b, c, p, q),
    )


@theorem
def enumeration_partition[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]],
    laws: Equivalence[A, R],
    h: Nat,
    xs: List[A],
    sizes: Pi[A, lambda a: Eq[Nat, class_size(dec, a, xs), h]],
) -> Divisible(h, length(xs)):
    r"""Apply uniform partition divisibility to a complete finite enumeration."""
    return uniform_partition(dec, laws, h, xs, lambda a: lambda member: sizes(a))


@dependent
def coset_decide[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A
) -> Decision[Related(g, h, a, b)]:
    r"""Decide the coset relation with the subgroup membership decision procedure."""
    return h.decide(g.op(g.inverse(a))(b))


@theorem
def lagrange[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    finite: Enumeration[A],
) -> Divisible(count(h.decide, finite.elements), length(finite.elements)):
    r"""Lagrange's theorem: :math:`|H| \mid |G|` for a finite group ``G`` and subgroup ``H``.

    Every coset has the subgroup cardinality by coset_size.
    Apply uniform partition divisibility to the complete group enumeration.
    """
    return enumeration_partition[A, lambda a: lambda b: Related(g, h, a, b)](
        lambda a: lambda b: coset_decide(g, h, a, b),
        coset_equivalence(g, h),
        count(h.decide, finite.elements),
        finite.elements,
        lambda a: coset_size(g, h, finite, a),
    )


# Concrete instances: the two-element group, with its trivial and whole
# subgroups. Both conclusions are applications of the general theorem.


@dependent
def zero_decide(x: Bit) -> Decision[IsZero(x)]:
    r"""Decide membership in the identity-only subgroup by case analysis on Bit."""
    match x:
        case B0():
            return Yes(Unit_())
        case B1():
            return No(lambda p: p)


@theorem
def zero_closed(x: Bit, y: Bit, px: IsZero(x), py: IsZero(y)) -> IsZero(xor(x, y)):
    r"""The product of two identity elements is again the identity.

    Case analysis uses the membership proofs to exclude B1.
    """
    match x:
        case B0():
            return py
        case B1():
            return absurd(IsZero(xor(B1(), y)), px)


@dependent
def trivial_subgroup() -> Subgroup[Bit, bit_group()]:
    r"""Construct the identity-only subgroup of the two-element group."""
    return Subgroup[Bit, bit_group()](
        lambda x: IsZero(x),
        lambda x: zero_decide(x),
        Unit_(),
        lambda x: lambda y: lambda px: lambda py: zero_closed(x, y, px, py),
        lambda x: lambda px: px,
    )


@dependent
def whole_subgroup() -> Subgroup[Bit, bit_group()]:
    r"""Construct the whole two-element group as its own subgroup."""
    return Subgroup[Bit, bit_group()](
        lambda x: Unit,
        lambda x: Yes(Unit_()),
        Unit_(),
        lambda x: lambda y: lambda px: lambda py: Unit_(),
        lambda x: lambda px: Unit_(),
    )


@theorem
def lagrange_trivial_example() -> Divisible(1, 2):
    r"""Apply Lagrange to the identity-only subgroup, proving that 1 divides 2."""
    return lagrange(bit_group(), trivial_subgroup(), bit_enumeration())


@theorem
def lagrange_whole_example() -> Divisible(2, 2):
    r"""Apply Lagrange to the whole subgroup, proving that 2 divides 2."""
    return lagrange(bit_group(), whole_subgroup(), bit_enumeration())
