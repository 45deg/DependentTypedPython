from __future__ import annotations
from deppy import (
    dependent,
    theorem,
    inductive,
    constructor,
    record,
    Index,
    Type,
    Pi,
    Sigma,
    Pair,
    Nat,
    Z,
    S,
    Eq,
    refl,
    J,
    induct,
    absurd,
)
from deppy.equality import sym, trans, cong, transport
from deppy.tactics import rewrite, rewrite_in
from deppy.nat import add, add_swap
from deppy.finite import (
    Enumeration,
    Removal,
    RemoveHere,
    RemoveThere,
    either_elim,
    find_removal,
    removal_present,
    removal_include,
    removal_keep,
    removal_nodup,
    removal_absent,
    removal_count,
    tail_forward,
    tail_backward,
    SameCountAt,
    same_count_nil,
    same_count_step,
    same_count,
    map_has,
    map_injective_has,
    map_nodup,
    inverse_injective,
    bijection_count,
    count_map,
    weight_unique,
    weight_transport,
)

# Shared finite enumeration, group, and finite-product definitions.
# All theorem bodies are checked; no additional axioms are introduced.

# Re-export the standard carriers so the finite examples share their nominal types.
from deppy.data import (
    Empty, Unit, MkUnit as Unit_, Not, Sum as Either, Left, Right,
    Decidable as Decision, Yes, No, decision_weight, weight_yes, weight_no,
)
from deppy.lists import (
    List, Nil, Cons, length, Mem as Has, NoDup, count,
    reject_head, reject, map,
)


# Group laws are inputs, not global axioms.
@record
class Group[A: Type]:
    r"""A group structure on carrier ``A``.

    :ivar unit: Identity element :math:`e`.
    :ivar op: Curried multiplication :math:`A \to A \to A`.
    :ivar inverse: Inversion :math:`a \mapsto a^{-1}`.
    :ivar assoc: Associativity, :math:`(ab)c=a(bc)`.
    :ivar left_unit: Left identity law, :math:`ea=a`.
    :ivar right_unit: Right identity law, :math:`ae=a`.
    :ivar left_inverse: Left inverse law, :math:`a^{-1}a=e`.
    :ivar right_inverse: Right inverse law, :math:`aa^{-1}=e`.
    """
    unit: A
    op: Pi[A, lambda x: Pi[A, lambda y: A]]
    inverse: Pi[A, lambda x: A]
    assoc: Pi[
        A,
        lambda x: Pi[
            A,
            lambda y: Pi[A, lambda z: Eq[A, self.op(self.op(x)(y))(z), self.op(x)(self.op(y)(z))]],
        ],
    ]
    left_unit: Pi[A, lambda x: Eq[A, self.op(self.unit)(x), x]]
    right_unit: Pi[A, lambda x: Eq[A, self.op(x)(self.unit), x]]
    left_inverse: Pi[A, lambda x: Eq[A, self.op(self.inverse(x))(x), self.unit]]
    right_inverse: Pi[A, lambda x: Eq[A, self.op(x)(self.inverse(x)), self.unit]]


@record(level=1)
class Subgroup[A: Type, g: Group[A]]:
    r"""A decidable subgroup of ``g``.

    :ivar member: Membership proposition on the carrier.
    :ivar decide: Decision procedure for membership.
    :ivar unit_closed: Evidence that the identity is a member.
    :ivar mul_closed: Closure under multiplication.
    :ivar inv_closed: Closure under inversion.
    """
    member: Pi[A, lambda _: Type]
    decide: Pi[A, lambda x: Decision[self.member(x)]]
    unit_closed: self.member(g.unit)
    mul_closed: Pi[
        A,
        lambda x: Pi[
            A,
            lambda y: Pi[
                self.member(x), lambda px: Pi[self.member(y), lambda py: self.member(g.op(x)(y))]
            ],
        ],
    ]
    inv_closed: Pi[A, lambda x: Pi[self.member(x), lambda _: self.member(g.inverse(x))]]


@theorem
def left_recover[A: Type](g: Group[A], a: A, x: A) -> Eq[A, g.op(g.inverse(a))(g.op(a)(x)), x]:
    r"""Cancel left multiplication by a using multiplication by its inverse.

    Reassociate, apply the left inverse law, and remove the identity.
    """
    return trans(
        sym(g.assoc(g.inverse(a))(a)(x)),
        trans(cong(lambda y: g.op(y)(x), g.left_inverse(a)), g.left_unit(x)),
    )


@theorem
def right_recover[A: Type](g: Group[A], a: A, x: A) -> Eq[A, g.op(a)(g.op(g.inverse(a))(x)), x]:
    r"""Undo left multiplication by the inverse of a.

    Reassociate, apply the right inverse law, and remove the identity.
    """
    return trans(
        sym(g.assoc(a)(g.inverse(a))(x)),
        trans(cong(lambda y: g.op(y)(x), g.right_inverse(a)), g.left_unit(x)),
    )


@inductive
class Bit:
    r"""The two elements used for the concrete group and nonzero elements of F_3."""
    @constructor
    def B0() -> Bit: ...
    @constructor
    def B1() -> Bit: ...


@dependent
def flip(x: Bit) -> Bit:
    r"""Exchange the two elements of Bit."""
    match x:
        case B0():
            return B1()
        case B1():
            return B0()


@dependent
def xor(x: Bit, y: Bit) -> Bit:
    r"""The two-element group operation, with B0 as identity."""
    match x:
        case B0():
            return y
        case B1():
            return flip(y)


@theorem
def xor_assoc(x: Bit, y: Bit, z: Bit) -> Eq[Bit, xor(xor(x, y), z), xor(x, xor(y, z))]:
    r"""Prove associativity of xor by case analysis on the three arguments."""
    match x:
        case B0():
            return refl(xor(y, z))
        case B1():
            match y:
                case B0():
                    return refl(flip(z))
                case B1():
                    match z:
                        case B0():
                            return refl(B0())
                        case B1():
                            return refl(B1())


@theorem
def xor_zero(x: Bit) -> Eq[Bit, xor(x, B0()), x]:
    r"""Prove that B0 is a right identity by case analysis."""
    match x:
        case B0():
            return refl(B0())
        case B1():
            return refl(B1())


@theorem
def xor_self(x: Bit) -> Eq[Bit, xor(x, x), B0()]:
    r"""Prove that each Bit is its own inverse by case analysis."""
    match x:
        case B0():
            return refl(B0())
        case B1():
            return refl(B0())


@dependent
def bit_group() -> Group[Bit]:
    r"""Construct the two-element group with xor and self-inverse elements."""
    return Group[Bit](
        B0(),
        lambda x: lambda y: xor(x, y),
        lambda x: x,
        lambda x: lambda y: lambda z: xor_assoc(x, y, z),
        lambda x: refl(x),
        lambda x: xor_zero(x),
        lambda x: xor_self(x),
        lambda x: xor_self(x),
    )


@dependent(decreases="x", motive_level=1)
def IsZero(x: Bit) -> Type:
    r"""A proposition inhabited for B0 and empty for B1."""
    match x:
        case B0():
            return Unit
        case B1():
            return Empty


@theorem
def zero_not_one(p: Eq[Bit, B0(), B1()]) -> Empty:
    r"""Refute equality of the two constructors by transporting Unit into Empty."""
    return transport[Bit, B0(), B1()](lambda x: IsZero(x), p, Unit_())


@dependent
def bit_elements() -> List[Bit]:
    r"""Enumerate the two elements once each, in B0, B1 order."""
    return Cons(B0(), Cons(B1(), Nil()))


@theorem
def bit_complete(x: Bit) -> Has(x, bit_elements()):
    r"""Prove that every Bit occurs in bit_elements by case analysis."""
    match x:
        case B0():
            return Left(refl(B0()))
        case B1():
            return Right(Left(refl(B1())))


@dependent
def bit_enumeration() -> Enumeration[Bit]:
    r"""Package the two-element list with duplicate-freeness and completeness proofs."""
    return Enumeration[Bit](
        bit_elements(),
        Pair(
            lambda p: either_elim[Eq[Bit, B0(), B1()], Empty, Empty](
                p, lambda eq: zero_not_one(eq), lambda empty: empty
            ),
            Pair(lambda empty: empty, Unit_()),
        ),
        lambda x: bit_complete(x),
    )


@dependent(decreases="n")
def power[A: Type](g: Group[A], a: A, n: Nat) -> A:
    r"""Define a natural power by repeated left multiplication, with exponent zero the identity."""
    match n:
        case Z():
            return g.unit
        case S(k):
            return g.op(a)(power(g, a, k))


@dependent(decreases="xs")
def product[A: Type, B: Type](g: Group[B], f: Pi[A, lambda _: B], xs: List[A]) -> B:
    r"""Multiply mapped list entries in order, using the identity for the empty list."""
    match xs:
        case Nil():
            return g.unit
        case Cons(x, tail):
            return g.op(f(x))(product(g, f, tail))


@theorem
def swap_factors[A: Type](
    g: Group[A], x: A, y: A, z: A, commute: Eq[A, g.op(x)(y), g.op(y)(x)]
) -> Eq[A, g.op(x)(g.op(y)(z)), g.op(y)(g.op(x)(z))]:
    r"""Exchange two commuting leading factors under a common right factor.

    Reassociate, rewrite by commutativity, and reassociate back.
    """
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
    r"""Separate a removed factor from the product when mapped factors commute.

    Induct on removal and move the removed factor past each preceding factor.
    """
    match r:
        case RemoveHere(tail):
            return refl(g.op(f(x))(product(g, f, tail)))
        case RemoveThere(head, before, after, step):
            return rewrite(
                removal_product(g, f, commute, step),
                swap_factors(g, f(head), f(x), product(g, f, after), commute(head)(x)),
            )


@dependent
def SameProductAt[A: Type, B: Type](g: Group[B], f: Pi[A, lambda _: B], xs: List[A]) -> Type:
    r"""State product invariance for duplicate-free lists with the same members."""
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
    r"""A list with no possible members has the identity as its product.

    The nonempty case contradicts membership of its head.
    """
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
    r"""Prove the inductive step for product invariance under reordering.

    Remove the matching head, use the tail hypothesis, and restore its factor.
    """
    found = find_removal(x, ys, forward(x)(Left(refl(x))))
    removal = found.snd
    proof = ih(found.fst)(ux.snd)(removal_nodup(removal, uy))(
        lambda q: lambda member: tail_forward(removal, ux, forward, q, member)
    )(lambda q: lambda member: tail_backward(removal, uy, backward, q, member))
    return rewrite(proof, sym(removal_product(g, f, commute, removal)))


@theorem
def same_product[A: Type, B: Type](
    g: Group[B],
    f: Pi[A, lambda _: B],
    commute: Pi[A, lambda u: Pi[A, lambda v: Eq[B, g.op(f(u))(f(v)), g.op(f(v))(f(u))]]],
    xs: List[A],
) -> SameProductAt(g, f, xs):
    r"""Reordering a duplicate-free list preserves a product of commuting factors.

    Induct on the first list and remove its head from the second.
    """
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
    r"""A carrier bijection preserves the complete product of commuting mapped values.

    Use the inverse to prove the mapped enumeration is complete and duplicate-free.
    """
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
    r"""From x multiplied by y equaling y, derive that x is the identity.

    Multiply on the right by the inverse of y and simplify using the group laws.
    """
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
    r"""Subtract one from a natural number, leaving zero unchanged."""
    match n:
        case Z():
            return 0
        case S(k):
            return k
