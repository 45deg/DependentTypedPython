from __future__ import annotations

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
#   --elaboration-steps 100000000 crates/deppy-python/examples/fermat.py

from deppy import dependent, theorem, Type, Pi, Sigma, Pair, Nat, Z, S, Eq, refl, induct, absurd
from deppy.equality import sym, trans, cong, transport
from deppy.nat import add, mul
from lagrange import (
    Group,
    Subgroup,
    Enumeration,
    count,
    length,
    lagrange,
    List,
    Nil,
    Cons,
    Has,
    NoDup,
    Empty,
    Unit,
    Unit_,
    Not,
    Left,
    Right,
    Decision,
    Yes,
    No,
    Removal,
    RemoveHere,
    RemoveThere,
    find_removal,
    removal_nodup,
    tail_forward,
    tail_backward,
    map,
    map_nodup,
    map_has,
    inverse_injective,
    left_recover,
    right_recover,
    either_elim,
    decision_weight,
    Bit,
    B0,
    B1,
    bit_group,
    bit_enumeration,
)


@dependent(decreases="n")
def power[A: Type](g: Group[A], a: A, n: Nat) -> A:
    match n:
        case Z():
            return g.unit
        case S(k):
            return g.op(a)(power(g, a, k))


@theorem(decreases="n")
def power_add[A: Type](
    g: Group[A], a: A, n: Nat, m: Nat
) -> Eq[A, power(g, a, add(n, m)), g.op(power(g, a, n))(power(g, a, m))]:
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
    quotient = lagrange(g, h, finite)
    return trans(
        cong(lambda n: power(g, a, n), quotient.snd),
        period_multiple(g, a, count(h.decide, finite.elements), period, quotient.fst),
    )


@dependent(decreases="xs")
def product[A: Type, B: Type](g: Group[B], f: Pi[A, lambda _: B], xs: List[A]) -> B:
    match xs:
        case Nil():
            return g.unit
        case Cons(x, tail):
            return g.op(f(x))(product(g, f, tail))


@theorem
def swap_factors[A: Type](
    g: Group[A], x: A, y: A, z: A, commute: Eq[A, g.op(x)(y), g.op(y)(x)]
) -> Eq[A, g.op(x)(g.op(y)(z)), g.op(y)(g.op(x)(z))]:
    return trans(
        sym(g.assoc(x)(y)(z)),
        trans(cong(lambda t: g.op(t)(z), commute), g.assoc(y)(x)(z)),
    )


@theorem(decreases="r")
def removal_product[A: Type, B: Type, x: A, ys: List[A], zs: List[A]](
    g: Group[B],
    f: Pi[A, lambda _: B],
    commute: Pi[A, lambda u: Pi[A, lambda v: Eq[B, g.op(f(u))(f(v)), g.op(f(v))(f(u))]]],
    r: Removal[A, x, ys, zs],
) -> Eq[B, product(g, f, ys), g.op(f(x))(product(g, f, zs))]:
    match r:
        case RemoveHere(tail):
            return refl(g.op(f(x))(product(g, f, tail)))
        case RemoveThere(head, before, after, step):
            return trans(
                cong(lambda t: g.op(f(head))(t), removal_product(g, f, commute, step)),
                swap_factors(g, f(head), f(x), product(g, f, after), commute(head)(x)),
            )


@dependent
def SameProductAt[A: Type, B: Type](g: Group[B], f: Pi[A, lambda _: B], xs: List[A]) -> Type:
    return Pi[
        List[A],
        lambda ys: Pi[
            NoDup(xs),
            lambda ux: Pi[
                NoDup(ys),
                lambda uy: Pi[
                    Pi[A, lambda q: Pi[Has(q, xs), lambda _: Has(q, ys)]],
                    lambda forward: Pi[
                        Pi[A, lambda q: Pi[Has(q, ys), lambda _: Has(q, xs)]],
                        lambda backward: Eq[B, product(g, f, xs), product(g, f, ys)],
                    ],
                ],
            ],
        ],
    ]


@theorem
def same_product_nil[A: Type, B: Type](
    g: Group[B],
    f: Pi[A, lambda _: B],
    ys: List[A],
    backward: Pi[A, lambda x: Pi[Has(x, ys), lambda _: Empty]],
) -> Eq[B, g.unit, product(g, f, ys)]:
    match ys:
        case Nil():
            return refl(g.unit)
        case Cons(y, tail):
            return absurd(Eq[B, g.unit, product(g, f, Cons(y, tail))], backward(y)(Left(refl(y))))


@theorem
def same_product_step[A: Type, B: Type](
    g: Group[B],
    f: Pi[A, lambda _: B],
    commute: Pi[A, lambda u: Pi[A, lambda v: Eq[B, g.op(f(u))(f(v)), g.op(f(v))(f(u))]]],
    x: A,
    tail: List[A],
    ih: SameProductAt(g, f, tail),
    ys: List[A],
    ux: NoDup(Cons(x, tail)),
    uy: NoDup(ys),
    forward: Pi[A, lambda q: Pi[Has(q, Cons(x, tail)), lambda _: Has(q, ys)]],
    backward: Pi[A, lambda q: Pi[Has(q, ys), lambda _: Has(q, Cons(x, tail))]],
) -> Eq[B, product(g, f, Cons(x, tail)), product(g, f, ys)]:
    found = find_removal(x, ys, forward(x)(Left(refl(x))))
    removal = found.snd
    proof = ih(found.fst)(ux.snd)(removal_nodup(removal, uy))(
        lambda q: lambda member: tail_forward(removal, ux, forward, q, member)
    )(lambda q: lambda member: tail_backward(removal, uy, backward, q, member))
    return trans(
        cong(lambda value: g.op(f(x))(value), proof),
        sym(removal_product(g, f, commute, removal)),
    )


@theorem
def same_product[A: Type, B: Type](
    g: Group[B],
    f: Pi[A, lambda _: B],
    commute: Pi[A, lambda u: Pi[A, lambda v: Eq[B, g.op(f(u))(f(v)), g.op(f(v))(f(u))]]],
    xs: List[A],
) -> SameProductAt(g, f, xs):
    return induct(
        0,
        xs,
        lambda zs: SameProductAt(g, f, zs),
        lambda ys: (
            lambda ux: (
                lambda uy: lambda forward: lambda backward: same_product_nil(g, f, ys, backward)
            )
        ),
        lambda x, tail, ih: (
            lambda ys: (
                lambda ux: (
                    lambda uy: (
                        lambda forward: (
                            lambda backward: same_product_step(
                                g, f, commute, x, tail, ih, ys, ux, uy, forward, backward
                            )
                        )
                    )
                )
            )
        ),
    )


@theorem
def bijection_product[A: Type, B: Type](
    g: Group[B],
    f: Pi[A, lambda _: B],
    commute: Pi[A, lambda u: Pi[A, lambda v: Eq[B, g.op(f(u))(f(v)), g.op(f(v))(f(u))]]],
    move: Pi[A, lambda _: A],
    back: Pi[A, lambda _: A],
    left: Pi[A, lambda x: Eq[A, back(move(x)), x]],
    right: Pi[A, lambda x: Eq[A, move(back(x)), x]],
    finite: Enumeration[A],
) -> Eq[B, product(g, f, map(move, finite.elements)), product(g, f, finite.elements)]:
    return same_product(g, f, commute, map(move, finite.elements))(finite.elements)(
        map_nodup(
            move,
            lambda x: lambda y: lambda eq: inverse_injective(move, back, left, x, y, eq),
            finite.elements,
            finite.unique,
        )
    )(finite.unique)(lambda x: lambda member: finite.complete(x))(
        lambda x: (
            lambda member: transport[A, move(back(x)), x](
                lambda q: Has(q, map(move, finite.elements)),
                right(x),
                map_has(move, back(x), finite.elements, finite.complete(back(x))),
            )
        )
    )


@dependent
def selected[A: Type, P: Type](g: Group[A], x: A, d: Decision[P]) -> A:
    match d:
        case Yes(p):
            return x
        case No(np):
            return g.unit


@theorem
def selected_yes[A: Type, P: Type](
    g: Group[A], x: A, d: Decision[P], p: P
) -> Eq[A, selected(g, x, d), x]:
    match d:
        case Yes(q):
            return refl(x)
        case No(np):
            return absurd(Eq[A, g.unit, x], np(p))


@theorem
def selected_no[A: Type, P: Type](
    g: Group[A], x: A, d: Decision[P], np: Not(P)
) -> Eq[A, selected(g, x, d), g.unit]:
    match d:
        case Yes(p):
            return absurd(Eq[A, x, g.unit], np(p))
        case No(nq):
            return refl(g.unit)


@theorem
def selected_member[A: Type](
    g: Group[A], h: Subgroup[A, g], x: A, d: Decision[h.member(x)]
) -> h.member(selected(g, x, d)):
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
def cancel_product[A: Type](g: Group[A], x: A, y: A, eq: Eq[A, g.op(x)(y), y]) -> Eq[A, x, g.unit]:
    return trans(
        sym(g.right_unit(x)),
        trans(
            cong(lambda t: g.op(x)(t), sym(g.right_inverse(y))),
            trans(
                sym(g.assoc(x)(y)(g.inverse(y))),
                trans(cong(lambda t: g.op(t)(g.inverse(y)), eq), g.right_inverse(y)),
            ),
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
    return equality_in_list(
        finite.elements, finite.unique, x, y, finite.complete(x), finite.complete(y)
    )


@dependent(decreases="xs", motive_level=1)
def All[A: Type, P: Pi[A, lambda _: Type]](xs: List[A]) -> Type:
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[P(x), lambda _: All(tail)]


@theorem
def decide_pair[P: Type, Q: Type](
    dp: Decision[P], dq: Decision[Q]
) -> Decision[Sigma[P, lambda _: Q]]:
    match dp:
        case Yes(p):
            match dq:
                case Yes(q):
                    return Yes[Sigma[P, lambda _: Q]](Pair(p, q))
                case No(nq):
                    return No[Sigma[P, lambda _: Q]](lambda both: nq(both.snd))
        case No(np):
            return No[Sigma[P, lambda _: Q]](lambda both: np(both.fst))


@theorem(decreases="xs")
def all_decide[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]],
    xs: List[A],
) -> Decision[All[A, P](xs)]:
    match xs:
        case Nil():
            return Yes(Unit_())
        case Cons(x, tail):
            return decide_pair(dec(x), all_decide(dec, tail))


@theorem(decreases="xs")
def all_intro[A: Type, P: Pi[A, lambda _: Type]](
    each: Pi[A, lambda x: P(x)],
    xs: List[A],
) -> All[A, P](xs):
    match xs:
        case Nil():
            return Unit_()
        case Cons(x, tail):
            return Pair(each(x), all_intro(each, tail))


@theorem(decreases="xs")
def all_get[A: Type, P: Pi[A, lambda _: Type]](
    xs: List[A],
    each: All[A, P](xs),
    x: A,
    member: Has(x, xs),
) -> P(x):
    match xs:
        case Nil():
            return absurd(P(x), member)
        case Cons(head, tail):
            return either_elim[Eq[A, x, head], Has(x, tail), P(x)](
                member,
                lambda eq: transport[A, head, x](P, sym(eq), each.fst),
                lambda rest: all_get(tail, each.snd, x, rest),
            )


@theorem
def implication_decide[P: Type, Q: Type](
    dp: Decision[P], dq: Decision[Q]
) -> Decision[Pi[P, lambda _: Q]]:
    match dp:
        case Yes(p):
            match dq:
                case Yes(q):
                    return Yes[Pi[P, lambda _: Q]](lambda _: q)
                case No(nq):
                    return No[Pi[P, lambda _: Q]](lambda f: nq(f(p)))
        case No(np):
            return Yes[Pi[P, lambda _: Q]](lambda p: absurd(Q, np(p)))


@dependent
def Commutes[A: Type](g: Group[A], x: A, y: A) -> Type:
    return Eq[A, g.op(x)(y), g.op(y)(x)]


# The center of the centralizer of a is an abelian subgroup containing a.
# This avoids assuming a cyclic-subgroup enumeration or an element order.
@dependent
def Central[A: Type](g: Group[A], finite: Enumeration[A], a: A, x: A) -> Type:
    return Sigma[
        Commutes(g, x, a),
        lambda _: All[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, x, y)]](
            finite.elements
        ),
    ]


@theorem
def central_decide[A: Type](
    g: Group[A], finite: Enumeration[A], a: A, x: A
) -> Decision[Central(g, finite, a, x)]:
    return decide_pair(
        equality_decide(finite, g.op(x)(a), g.op(a)(x)),
        all_decide[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, x, y)]](
            lambda y: implication_decide(
                equality_decide(finite, g.op(y)(a), g.op(a)(y)),
                equality_decide(finite, g.op(x)(y), g.op(y)(x)),
            ),
            finite.elements,
        ),
    )


@theorem
def commute_unit[A: Type](g: Group[A], x: A) -> Commutes(g, g.unit, x):
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
    return Pair(
        commute_unit(g, a),
        all_intro[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, g.unit, y)]](
            lambda y: lambda _: commute_unit(g, y), finite.elements
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
    return all_get[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, x, y)]](
        finite.elements, px.snd, y, finite.complete(y)
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
    return Pair(
        commute_mul(g, x, y, a, px.fst, py.fst),
        all_intro[A, lambda z: Pi[Commutes(g, z, a), lambda _: Commutes(g, g.op(x)(y), z)]](
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
            finite.elements,
        ),
    )


@theorem
def central_inverse[A: Type](
    g: Group[A], finite: Enumeration[A], a: A, x: A, px: Central(g, finite, a, x)
) -> Central(g, finite, a, g.inverse(x)):
    return Pair(
        commute_inverse(g, x, a, px.fst),
        all_intro[A, lambda z: Pi[Commutes(g, z, a), lambda _: Commutes(g, g.inverse(x), z)]](
            lambda z: lambda pz: commute_inverse(g, x, z, central_get(g, finite, a, x, px, z, pz)),
            finite.elements,
        ),
    )


@theorem
def central_self[A: Type](g: Group[A], finite: Enumeration[A], a: A) -> Central(g, finite, a, a):
    return Pair(
        refl(g.op(a)(a)),
        all_intro[A, lambda y: Pi[Commutes(g, y, a), lambda _: Commutes(g, a, y)]](
            lambda y: lambda py: sym(py), finite.elements
        ),
    )


@dependent
def central_subgroup[A: Type](g: Group[A], finite: Enumeration[A], a: A) -> Subgroup[A, g]:
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


@dependent
def predecessor(n: Nat) -> Nat:
    match n:
        case Z():
            return 0
        case S(k):
            return k


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
    exponent = cong(lambda n: predecessor(n), cardinality)
    return trans(
        cong(lambda n: power(multiplication, a, n), sym(exponent)),
        finite_group_power(multiplication, nonzero, a),
    )


# F_3^* has two elements: B0 represents 1, B1 represents -1 = 2.
# Its multiplication table is the two-element group checked in lagrange.py.
@theorem
def fermat_three(a: Bit) -> Eq[Bit, power(bit_group(), a, 2), B0()]:
    return fermat_little(bit_group(), bit_enumeration(), 3, refl(3), a)


@theorem
def fermat_three_two() -> Eq[Bit, power(bit_group(), B1(), 2), B0()]:
    return fermat_three(B1())
