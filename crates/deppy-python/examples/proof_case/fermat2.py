from __future__ import annotations

# Direct finite-field proof: multiplication by a permutes the nonzero elements,
# so P = a^(p-1) * P; cancel P. The carrier contains only nonzero elements.
# We require a finite commutative group and its cardinality, not a power identity.
# No use of the Lagrange theorem or of fermat.py.
# Check: cargo run -p deppy-python --locked --offline -- \
#     crates/deppy-python/examples/proof_case/fermat2.py

from deppy import theorem, Type, Pi, Nat, S, Eq, refl
from deppy.equality import sym, trans, cong
from deppy.tactics import rewrite
from common import (
    B0,
    B1,
    Bit,
    Cons,
    Enumeration,
    Group,
    List,
    Nil,
    bijection_product,
    bit_enumeration,
    bit_group,
    cancel_product,
    left_recover,
    length,
    map,
    power,
    predecessor,
    product,
    right_recover,
    swap_factors,
)


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
    r"""Left translation by a extracts one copy of a per list entry.

    Induct on the list; commutativity moves each entry past the accumulated power.
    """
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
    r"""Direct finite-abelian-group theorem: :math:`a^{|G|}=e`.

    This proof permutes the complete product and does not use Lagrange's theorem.

    Left translation permutes the full enumeration. Compare its product with
    the scaled product and cancel the common right factor.
    """
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
    r"""Direct-product proof of Fermat's little theorem, :math:`a^{p-1}=1`.

    Use the supplied cardinality to rewrite p - 1 to the enumeration length,
    then apply finite_abelian_power.
    """
    return rewrite(
        sym(cardinality),
        finite_abelian_power(multiplication, commute, nonzero, a),
    )


# F_3^*: B0 represents 1 and B1 represents 2. These are checked applications
# of the generic theorem, not separate calculations of the example's power.
@theorem
def bit_commute(x: Bit, y: Bit) -> Eq[Bit, bit_group().op(x)(y), bit_group().op(y)(x)]:
    r"""Prove commutativity of the two-element group by checking both arguments."""
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
    r"""Apply the finite abelian group theorem to the two nonzero elements of F_3.

    The explicit enumeration and reflexivity prove the required cardinality.
    """
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
    r"""Specialize the F_3 theorem to B1, which represents the nonzero element 2."""
    return fermat_three(B1())
