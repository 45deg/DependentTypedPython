from __future__ import annotations

# Direct finite-field proof: multiplication by a permutes the nonzero elements,
# so P = a^(p-1) * P; cancel P. The carrier contains only nonzero elements.
# We require a finite commutative group and its cardinality, not a power identity.
# No use of the Lagrange theorem or of fermat.py.
# Check: cargo run -p deppy-python --locked --offline -- \
#     crates/deppy-python/examples/fermat2.py

from deppy import dependent, theorem, Type, Pi, Nat, Z, S, Eq, refl, induct, absurd
from deppy.equality import sym, trans, cong, transport
from lagrange import (
    Group,
    Enumeration,
    List,
    Nil,
    Cons,
    Has,
    NoDup,
    Empty,
    Left,
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
    length,
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


@dependent
def predecessor(n: Nat) -> Nat:
    match n:
        case Z():
            return 0
        case S(k):
            return k


# Pull one copy of a out of every factor of the product.
@theorem(decreases="xs")
def product_scale[A: Type](
    g: Group[A],
    commute: Pi[A, lambda x: Pi[A, lambda y: Eq[A, g.op(x)(y), g.op(y)(x)]]],
    a: A,
    xs: List[A],
) -> Eq[
    A,
    product(g, lambda x: x, map(lambda x: g.op(a)(x), xs)),
    g.op(power(g, a, length(xs)))(product(g, lambda x: x, xs)),
]:
    match xs:
        case Nil():
            return sym(g.left_unit(g.unit))
        case Cons(x, tail):
            rest = product(g, lambda y: y, tail)
            factor = power(g, a, length(tail))
            return trans(
                cong(lambda t: g.op(g.op(a)(x))(t), product_scale(g, commute, a, tail)),
                trans(
                    g.assoc(a)(x)(g.op(factor)(rest)),
                    trans(
                        cong(
                            lambda t: g.op(a)(t),
                            swap_factors(g, x, factor, rest, commute(x)(factor)),
                        ),
                        sym(g.assoc(a)(factor)(g.op(x)(rest))),
                    ),
                ),
            )


@theorem
def finite_abelian_power[A: Type](
    g: Group[A],
    commute: Pi[A, lambda x: Pi[A, lambda y: Eq[A, g.op(x)(y), g.op(y)(x)]]],
    finite: Enumeration[A],
    a: A,
) -> Eq[A, power(g, a, length(finite.elements)), g.unit]:
    permuted = bijection_product[A, A](
        g,
        lambda x: x,
        commute,
        lambda x: g.op(a)(x),
        lambda x: g.op(g.inverse(a))(x),
        lambda x: left_recover(g, a, x),
        lambda x: right_recover(g, a, x),
        finite,
    )
    scaled = product_scale(g, commute, a, finite.elements)
    return cancel_product(
        g,
        power(g, a, length(finite.elements)),
        product(g, lambda x: x, finite.elements),
        trans(sym(scaled), permuted),
    )


# For F_p^*, cardinality states that there are p-1 nonzero elements.
# This also proves the corresponding result for a field of prime-power size.
@theorem
def fermat_little[A: Type](
    multiplication: Group[A],
    commute: Pi[
        A, lambda x: Pi[A, lambda y: Eq[A, multiplication.op(x)(y), multiplication.op(y)(x)]]
    ],
    nonzero: Enumeration[A],
    p: Nat,
    cardinality: Eq[Nat, S(length(nonzero.elements)), p],
    a: A,
) -> Eq[A, power(multiplication, a, predecessor(p)), multiplication.unit]:
    exponent = cong(lambda n: predecessor(n), cardinality)
    return trans(
        cong(lambda n: power(multiplication, a, n), sym(exponent)),
        finite_abelian_power(multiplication, commute, nonzero, a),
    )


# F_3^*: B0 represents 1 and B1 represents 2. These are checked applications
# of the generic theorem, not separate calculations of the example's power.
@theorem
def bit_commute(x: Bit, y: Bit) -> Eq[Bit, bit_group().op(x)(y), bit_group().op(y)(x)]:
    match x:
        case B0():
            match y:
                case B0():
                    return refl(B0())
                case B1():
                    return refl(B1())
        case B1():
            match y:
                case B0():
                    return refl(B1())
                case B1():
                    return refl(B0())


@theorem
def fermat_three(a: Bit) -> Eq[Bit, power(bit_group(), a, 2), B0()]:
    return fermat_little(
        bit_group(),
        lambda x: lambda y: bit_commute(x, y),
        bit_enumeration(),
        3,
        refl(3),
        a,
    )


@theorem
def fermat_three_two() -> Eq[Bit, power(bit_group(), B1(), 2), B0()]:
    return fermat_three(B1())
