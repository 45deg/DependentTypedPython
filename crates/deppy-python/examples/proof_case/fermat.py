
# Finite-field formulation of Fermat's little theorem. The carrier is the
# NONZERO elements of the field, multiplication is a group operation, and
# p = 1 + the number of nonzero elements. No primality, modular arithmetic,
# cyclic subgroup, element order, or power identity is taken as an axiom.
# The argument also applies to finite fields of non-prime cardinality.
#
# Proof: construct the center of the centralizer of a; it is an abelian
# subgroup containing a. Multiplying its elements shows a^|H| = 1, and
# Lagrange gives |G| = |H| * k. Hence a^|G| = 1.
#
# cargo run -p deppy-python --locked --offline -- \
#   --elaboration-steps 100000000 crates/deppy-python/examples/proof_case/fermat.py

from deppy import dependent, theorem, Type, Pi, Sigma, Pair, Nat, Z, S, Eq, refl, absurd
from deppy.equality import sym, trans, cong, transport
from deppy.tactics import rewrite
from deppy.nat import add, mul
from deppy.data import decide_and, decide_implies
from deppy.lists import All, all_decide, all_intro, all_get
from common import (
    B0,
    B1,
    Bit,
    Cons,
    Decision,
    Enumeration,
    Group,
    Has,
    Left,
    List,
    Nil,
    No,
    NoDup,
    Not,
    Right,
    Subgroup,
    Yes,
    bijection_product,
    bit_enumeration,
    bit_group,
    cancel_product,
    count,
    decision_weight,
    left_recover,
    length,
    map,
    power,
    predecessor,
    product,
    right_recover,
    swap_factors,
)
from lagrange import lagrange


@theorem(decreases="n")
def power_add[A: Type](
    g: Group[A], a: A, n: Nat, m: Nat
) -> Eq[A, power(g, a, add(n, m)), g.op(power(g, a, n))(power(g, a, m))]:
    r"""Split a power at the sum of its exponents.

    Induct on the first exponent and reassociate the successor case.
    """
    match n:
        case Z():
            return sym(g.left_unit(power(g, a, m)))
        case S(k):
            return trans(
                cong(lambda x: g.op(a)(x), power_add(g, a, k, m)),
                sym(g.assoc(a)(power(g, a, k))(power(g, a, m))),
            )


@theorem(decreases="k")
def period_multiple[A: Type](
    g: Group[A], a: A, d: Nat, period: Eq[A, power(g, a, d), g.unit], k: Nat
) -> Eq[A, power(g, a, mul(d, k)), g.unit]:
    r"""If a to the power d is the identity, so is a to any multiple d*k.

    Induct on k, split the sum of exponents, and use the given period.
    """
    match k:
        case Z():
            return refl(g.unit)
        case S(j):
            return trans(
                power_add(g, a, d, mul(d, j)),
                trans(
                    cong(lambda x: g.op(x)(power(g, a, mul(d, j))), period),
                    trans(
                        g.left_unit(power(g, a, mul(d, j))),
                        period_multiple(g, a, d, period, j),
                    ),
                ),
            )


# Lagrange supplies the multiplier. The period for the subgroup must be proved
# separately; it is not an axiom and is not assumed for the ambient group.
@theorem
def lagrange_power[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    finite: Enumeration[A],
    a: A,
    period: Eq[A, power(g, a, count(h.decide, finite.elements)), g.unit],
) -> Eq[A, power(g, a, length(finite.elements)), g.unit]:
    r"""Lift a proved subgroup period to the size of the ambient finite group.

    Lagrange supplies the multiplier; rewrite the exponent and apply period_multiple.
    """
    quotient = lagrange(g, h, finite)
    return rewrite(
        quotient.snd,
        period_multiple(g, a, count(h.decide, finite.elements), period, quotient.fst),
    )


@dependent
def selected[A: Type, P: Type](g: Group[A], x: A, d: Decision[P]) -> A:
    r"""Keep a selected element, replacing an unselected element by the group identity."""
    match d:
        case Yes(p):
            return x
        case No(np):
            return g.unit


@theorem
def selected_yes[A: Type, P: Type](
    g: Group[A], x: A, d: Decision[P], p: P
) -> Eq[A, selected(g, x, d), x]:
    r"""A proof of the predicate forces selection of the original element.

    The negative decision branch is contradictory.
    """
    match d:
        case Yes(q):
            return refl(x)
        case No(np):
            return absurd(Eq[A, g.unit, x], np(p))


@theorem
def selected_no[A: Type, P: Type](
    g: Group[A], x: A, d: Decision[P], np: Not(P)
) -> Eq[A, selected(g, x, d), g.unit]:
    r"""A refutation forces selection of the group identity.

    The positive decision branch is contradictory.
    """
    match d:
        case Yes(p):
            return absurd(Eq[A, x, g.unit], np(p))
        case No(nq):
            return refl(g.unit)


@theorem
def selected_member[A: Type](
    g: Group[A], h: Subgroup[A, g], x: A, d: Decision[h.member(x)]
) -> h.member(selected(g, x, d)):
    r"""The selected value lies in H, whether it is the original member or the identity."""
    match d:
        case Yes(p):
            return p
        case No(np):
            return h.unit_closed


@theorem
def selected_commute[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    commute: Pi[
        A,
        lambda x: Pi[
            A,
            lambda y: Pi[
                h.member(x), lambda px: Pi[h.member(y), lambda py: Eq[A, g.op(x)(y), g.op(y)(x)]]
            ],
        ],
    ],
    x: A,
    y: A,
) -> Eq[
    A,
    g.op(selected(g, x, h.decide(x)))(selected(g, y, h.decide(y))),
    g.op(selected(g, y, h.decide(y)))(selected(g, x, h.decide(x))),
]:
    r"""Values selected into an abelian subgroup commute.

    Apply subgroup commutativity to their selection membership proofs.
    """
    return commute(selected(g, x, h.decide(x)))(selected(g, y, h.decide(y)))(
        selected_member(g, h, x, h.decide(x))
    )(selected_member(g, h, y, h.decide(y)))


@theorem(decreases="n")
def commute_power[A: Type](
    g: Group[A],
    a: A,
    x: A,
    commute: Eq[A, g.op(x)(a), g.op(a)(x)],
    n: Nat,
) -> Eq[A, g.op(x)(power(g, a, n)), g.op(power(g, a, n))(x)]:
    r"""An element commuting with a also commutes with every natural power of a.

    Induct on the exponent and exchange successive factors using associativity.
    """
    match n:
        case Z():
            return trans(g.right_unit(x), sym(g.left_unit(x)))
        case S(k):
            return trans(
                swap_factors(g, x, a, power(g, a, k), commute),
                trans(
                    cong(lambda t: g.op(a)(t), commute_power(g, a, x, commute, k)),
                    sym(g.assoc(a)(power(g, a, k))(x)),
                ),
            )


@theorem
def left_membership[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    a: A,
    pa: h.member(a),
    x: A,
    moved: h.member(g.op(a)(x)),
) -> h.member(x):
    r"""If a and a*x lie in H, then x lies in H.

    Multiply by inverse(a), use subgroup closure, and cancel a.
    """
    return transport[A, g.op(g.inverse(a))(g.op(a)(x)), x](
        h.member,
        left_recover(g, a, x),
        h.mul_closed(g.inverse(a))(g.op(a)(x))(h.inv_closed(a)(pa))(moved),
    )


@theorem
def scalar_step[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    a: A,
    pa: h.member(a),
    x: A,
    commute: Pi[h.member(x), lambda _: Eq[A, g.op(x)(a), g.op(a)(x)]],
    d: Decision[h.member(x)],
    n: Nat,
    z: A,
) -> Eq[
    A,
    g.op(selected(g, g.op(a)(x), h.decide(g.op(a)(x))))(g.op(power(g, a, n))(z)),
    g.op(power(g, a, add(decision_weight(d), n)))(g.op(selected(g, x, d))(z)),
]:
    r"""Extract one factor of a exactly when the current entry belongs to H.

    Split membership, using commutation in the positive case and cancellation in the negative.
    """
    match d:
        case Yes(px):
            return trans(
                cong(
                    lambda t: g.op(t)(g.op(power(g, a, n))(z)),
                    selected_yes(g, g.op(a)(x), h.decide(g.op(a)(x)), h.mul_closed(a)(x)(pa)(px)),
                ),
                trans(
                    g.assoc(a)(x)(g.op(power(g, a, n))(z)),
                    trans(
                        cong(
                            lambda t: g.op(a)(t),
                            swap_factors(
                                g, x, power(g, a, n), z, commute_power(g, a, x, commute(px), n)
                            ),
                        ),
                        sym(g.assoc(a)(power(g, a, n))(g.op(x)(z))),
                    ),
                ),
            )
        case No(np):
            return trans(
                cong(
                    lambda t: g.op(t)(g.op(power(g, a, n))(z)),
                    selected_no(
                        g,
                        g.op(a)(x),
                        h.decide(g.op(a)(x)),
                        lambda moved: np(left_membership(g, h, a, pa, x, moved)),
                    ),
                ),
                trans(
                    g.left_unit(g.op(power(g, a, n))(z)),
                    sym(cong(lambda t: g.op(power(g, a, n))(t), g.left_unit(z))),
                ),
            )


@theorem(decreases="xs")
def product_translate[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    a: A,
    pa: h.member(a),
    commute: Pi[A, lambda x: Pi[h.member(x), lambda _: Eq[A, g.op(x)(a), g.op(a)(x)]]],
    xs: List[A],
) -> Eq[
    A,
    product(g, lambda x: selected(g, x, h.decide(x)), map(lambda x: g.op(a)(x), xs)),
    g.op(power(g, a, count(h.decide, xs)))(product(g, lambda x: selected(g, x, h.decide(x)), xs)),
]:
    r"""Translating a list by a extracts a to the number of subgroup members.

    Assume a lies in H and commutes with its members; induct using scalar_step.
    """
    match xs:
        case Nil():
            return sym(g.left_unit(g.unit))
        case Cons(x, tail):
            return trans(
                cong(
                    lambda t: g.op(selected(g, g.op(a)(x), h.decide(g.op(a)(x))))(t),
                    product_translate(g, h, a, pa, commute, tail),
                ),
                scalar_step(
                    g,
                    h,
                    a,
                    pa,
                    x,
                    commute(x),
                    h.decide(x),
                    count(h.decide, tail),
                    product(g, lambda y: selected(g, y, h.decide(y)), tail),
                ),
            )


@theorem
def abelian_subgroup_period[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    finite: Enumeration[A],
    commute: Pi[
        A,
        lambda x: Pi[
            A,
            lambda y: Pi[
                h.member(x), lambda px: Pi[h.member(y), lambda py: Eq[A, g.op(x)(y), g.op(y)(x)]]
            ],
        ],
    ],
    a: A,
    pa: h.member(a),
) -> Eq[A, power(g, a, count(h.decide, finite.elements)), g.unit]:
    r"""Every element of a finite abelian subgroup satisfies a to the size of H = e.

    Translation permutes the selected product; extract the power and cancel the product.
    """
    invariant = bijection_product(
        g,
        lambda x: selected(g, x, h.decide(x)),
        lambda x: lambda y: selected_commute(g, h, commute, x, y),
        lambda x: g.op(a)(x),
        lambda x: g.op(g.inverse(a))(x),
        lambda x: left_recover(g, a, x),
        lambda x: right_recover(g, a, x),
        finite,
    )
    translated = product_translate(
        g, h, a, pa, lambda x: lambda px: commute(x)(a)(px)(pa), finite.elements
    )
    return cancel_product(
        g,
        power(g, a, count(h.decide, finite.elements)),
        product(g, lambda x: selected(g, x, h.decide(x)), finite.elements),
        trans(sym(translated), invariant),
    )


# A finite enumeration provides decidable equality without assuming it.
@theorem(decreases="xs")
def equality_in_list[A: Type](
    xs: List[A],
    unique: NoDup(xs),
    x: A,
    y: A,
    mx: Has(x, xs),
    my: Has(y, xs),
) -> Decision[Eq[A, x, y]]:
    r"""Decide equality of two members of a duplicate-free list.

    Follow both membership proofs; duplicate-freeness excludes unequal positions.
    """
    match xs:
        case Nil():
            return absurd(Decision[Eq[A, x, y]], mx)
        case Cons(head, tail):
            match mx:
                case Left(ex):
                    match my:
                        case Left(ey):
                            return Yes(trans(ex, sym(ey)))
                        case Right(py):
                            return No[Eq[A, x, y]](
                                lambda eq: unique.fst(
                                    transport[A, y, head](
                                        lambda q: Has(q, tail), trans(sym(eq), ex), py
                                    )
                                )
                            )
                case Right(px):
                    match my:
                        case Left(ey):
                            return No[Eq[A, x, y]](
                                lambda eq: unique.fst(
                                    transport[A, x, head](lambda q: Has(q, tail), trans(eq, ey), px)
                                )
                            )
                        case Right(py):
                            return equality_in_list(tail, unique.snd, x, y, px, py)


@theorem
def equality_decide[A: Type](finite: Enumeration[A], x: A, y: A) -> Decision[Eq[A, x, y]]:
    r"""Derive decidable equality from a complete duplicate-free enumeration.

    Completeness supplies the two membership proofs for equality_in_list.
    """
    return equality_in_list(
        finite.elements, finite.unique, x, y, finite.complete(x), finite.complete(y)
    )


@dependent
def Commutes[A: Type](g: Group[A], x: A, y: A) -> Type:
    r"""Express equality of the two orders of multiplication."""
    return Eq[A, g.op(x)(y), g.op(y)(x)]


# The center of the centralizer of a is an abelian subgroup containing a.
# This avoids assuming a cyclic-subgroup enumeration or an element order.
@dependent
def Central[A: Type](g: Group[A], finite: Enumeration[A], a: A, x: A) -> Type:
    r"""Express membership in the center of the centralizer of a.

    Require commutation with a and with every enumerated element commuting with a.
    """
    return Sigma[
        Commutes(g, x, a),
        lambda _: All(
            lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, x, y)],
            finite.elements,
        ),
    ]


@theorem
def central_decide[A: Type](
    g: Group[A], finite: Enumeration[A], a: A, x: A
) -> Decision[Central(g, finite, a, x)]:
    r"""Decide membership in the center of the centralizer using finite enumeration.

    Combine decidable equality, implication, and the list-wide decision procedure.
    """
    return decide_and(
        equality_decide(finite, g.op(x)(a), g.op(a)(x)),
        all_decide[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, x, y)]](
            lambda y: decide_implies(
                equality_decide(finite, g.op(y)(a), g.op(a)(y)),
                equality_decide(finite, g.op(x)(y), g.op(y)(x)),
            ),
            finite.elements,
        ),
    )


@theorem
def commute_unit[A: Type](g: Group[A], x: A) -> Commutes(g, g.unit, x):
    r"""The group identity commutes with every element by the two identity laws."""
    return trans(g.left_unit(x), sym(g.right_unit(x)))


@theorem
def commute_mul[A: Type](
    g: Group[A],
    x: A,
    y: A,
    z: A,
    px: Commutes(g, x, z),
    py: Commutes(g, y, z),
) -> Commutes(g, g.op(x)(y), z):
    r"""The product of two elements commuting with z also commutes with z.

    Reassociate and move z past each factor.
    """
    return trans[A, g.op(g.op(x)(y))(z), g.op(x)(g.op(y)(z)), g.op(z)(g.op(x)(y))](
        g.assoc(x)(y)(z),
        trans(
            cong(lambda t: g.op(x)(t), py),
            swap_factors(g, x, z, y, px),
        ),
    )


@theorem
def commute_inverse[A: Type](g: Group[A], x: A, z: A, px: Commutes(g, x, z)) -> Commutes(
    g, g.inverse(x), z
):
    r"""An inverse commutes with z whenever the original element does.

    Insert an inverse pair, exchange the commuting factors, and cancel.
    """
    return trans(
        cong(lambda t: g.op(g.inverse(x))(t), sym(g.right_unit(z))),
        trans(
            cong(lambda t: g.op(g.inverse(x))(g.op(z)(t)), sym(g.right_inverse(x))),
            trans(
                cong(lambda t: g.op(g.inverse(x))(t), sym(g.assoc(z)(x)(g.inverse(x)))),
                trans(
                    cong(lambda t: g.op(g.inverse(x))(g.op(t)(g.inverse(x))), sym(px)),
                    trans(
                        cong(lambda t: g.op(g.inverse(x))(t), g.assoc(x)(z)(g.inverse(x))),
                        left_recover(g, x, g.op(z)(g.inverse(x))),
                    ),
                ),
            ),
        ),
    )


@theorem
def central_unit[A: Type](g: Group[A], finite: Enumeration[A], a: A) -> Central(
    g, finite, a, g.unit
):
    r"""The identity lies in the center of the centralizer.

    Use its commutation law for a and every enumerated element.
    """
    return Pair(
        commute_unit(g, a),
        all_intro[A](
            lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, g.unit, y)],
            finite.elements,
            lambda y: lambda _: commute_unit(g, y),
        ),
    )


@theorem
def central_get[A: Type](
    g: Group[A],
    finite: Enumeration[A],
    a: A,
    x: A,
    px: Central(g, finite, a, x),
    y: A,
    py: Commutes(g, y, a),
) -> Commutes(g, x, y):
    r"""A central element commutes with any element commuting with a.

    Completeness locates that element in the stored list-wide evidence.
    """
    return all_get[A](
        lambda z: Pi[Commutes(g, z, a), lambda _: Commutes(g, x, z)],
        y,
        finite.elements,
        finite.complete(y),
        px.snd,
    )(py)


@theorem
def central_mul[A: Type](
    g: Group[A],
    finite: Enumeration[A],
    a: A,
    x: A,
    y: A,
    px: Central(g, finite, a, x),
    py: Central(g, finite, a, y),
) -> Central(g, finite, a, g.op(x)(y)):
    r"""The center of the centralizer is closed under multiplication.

    Apply commute_mul to a and to each element of its centralizer.
    """
    return Pair(
        commute_mul(g, x, y, a, px.fst, py.fst),
        all_intro[A](
            lambda z: Pi[Commutes(g, z, a), lambda _: Commutes(g, g.op(x)(y), z)],
            finite.elements,
            lambda z: (
                lambda pz: commute_mul(
                    g,
                    x,
                    y,
                    z,
                    central_get(g, finite, a, x, px, z, pz),
                    central_get(g, finite, a, y, py, z, pz),
                )
            ),
        ),
    )


@theorem
def central_inverse[A: Type](
    g: Group[A], finite: Enumeration[A], a: A, x: A, px: Central(g, finite, a, x)
) -> Central(g, finite, a, g.inverse(x)):
    r"""The center of the centralizer is closed under inverses.

    Apply commute_inverse to both parts of its membership evidence.
    """
    return Pair(
        commute_inverse(g, x, a, px.fst),
        all_intro[A](
            lambda z: Pi[Commutes(g, z, a), lambda _: Commutes(g, g.inverse(x), z)],
            finite.elements,
            lambda z: lambda pz: commute_inverse(g, x, z, central_get(g, finite, a, x, px, z, pz)),
        ),
    )


@theorem
def central_self[A: Type](g: Group[A], finite: Enumeration[A], a: A) -> Central(g, finite, a, a):
    r"""The element a belongs to the center of its own centralizer.

    Self-commutation is reflexive and the remaining requirements follow by symmetry.
    """
    return Pair(
        refl(g.op(a)(a)),
        all_intro[A](
            lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, a, y)],
            finite.elements,
            lambda y: lambda py: sym(py),
        ),
    )


@dependent
def central_subgroup[A: Type](g: Group[A], finite: Enumeration[A], a: A) -> Subgroup[A, g]:
    r"""Construct the decidable center-of-centralizer subgroup containing a.

    Package its membership decision, identity, multiplication, and inverse proofs.
    """
    return Subgroup[A, g](
        lambda x: Central(g, finite, a, x),
        lambda x: central_decide(g, finite, a, x),
        central_unit(g, finite, a),
        lambda x: lambda y: lambda px: lambda py: central_mul(g, finite, a, x, y, px, py),
        lambda x: lambda px: central_inverse(g, finite, a, x, px),
    )


@theorem
def finite_group_power[A: Type](
    g: Group[A], finite: Enumeration[A], a: A
) -> Eq[A, power(g, a, length(finite.elements)), g.unit]:
    r"""Finite-group power theorem: :math:`a^{|G|}=e` for every :math:`a\in G`.

    Use the center of the centralizer as an abelian subgroup containing a.
    Its product proof gives a subgroup period, which Lagrange lifts to the group size.
    """
    h = central_subgroup(g, finite, a)
    period = abelian_subgroup_period(
        g,
        h,
        finite,
        lambda x: lambda y: lambda px: lambda py: central_get(g, finite, a, x, px, y, py.fst),
        a,
        central_self(g, finite, a),
    )
    return lagrange_power(g, h, finite, a, period)


# This interface represents F_p^*: zero is not in the carrier A. The field's
# construction is independent of this multiplicative-group theorem.
@theorem
def fermat_little[A: Type](
    multiplication: Group[A],
    nonzero: Enumeration[A],
    p: Nat,
    cardinality: Eq[Nat, S(length(nonzero.elements)), p],
    a: A,
) -> Eq[A, power(multiplication, a, predecessor(p)), multiplication.unit]:
    r"""Fermat's little theorem in multiplicative-group form.

    If :math:`p=1+|G|`, then :math:`a^{p-1}=1` for every nonzero ``a``.

    Rewrite the supplied cardinality equality in the exponent and apply
    finite_group_power; no construction of a field or primality proof is assumed.
    """
    return rewrite(
        sym(cardinality),
        finite_group_power(multiplication, nonzero, a),
    )


# F_3^* has two elements: B0 represents 1, B1 represents -1 = 2.
# Its multiplication table is the two-element group checked in common.py.
@theorem
def fermat_three(a: Bit) -> Eq[Bit, power(bit_group(), a, 2), B0()]:
    r"""Fermat's theorem for the nonzero elements of :math:`\mathbf F_3`.

    Instantiate the group theorem with bit_group and its complete enumeration.
    """
    return fermat_little(bit_group(), bit_enumeration(), 3, refl(3), a)


@theorem
def fermat_three_two() -> Eq[Bit, power(bit_group(), B1(), 2), B0()]:
    r"""Specialize the F_3 theorem to B1, which represents the nonzero element 2."""
    return fermat_three(B1())
