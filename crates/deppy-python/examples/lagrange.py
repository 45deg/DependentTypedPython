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
    nat_elim,
)
from deppy.equality import sym, trans, cong, transport
from deppy.nat import add, mul, add_zero, add_succ, add_assoc, add_comm, add_swap
from deppy.nat_order import LE, LEZero, LESucc, le_refl, le_step, le_pred, le_trans

# A constructive, single-file development. No axioms or unchecked assertions.
# Finite enumerations contain each carrier element exactly once. Membership of
# the subgroup is decidable; no quotient type or choice principle is used.
# Check with: cargo run -p deppy-python --locked --offline -- \
#     crates/deppy-python/examples/lagrange.py
# Opaque lemmas have checked bodies; opacity only prevents their unfolding.


@inductive
class Empty:
    pass


@inductive
class Unit:
    @constructor
    def Unit_() -> Unit: ...


@dependent
def Not(P: Type) -> Type:
    return Pi[P, lambda _: Empty]


@inductive
class Either[A: Type, B: Type]:
    @constructor
    def Left(value: A) -> Either[A, B]: ...
    @constructor
    def Right(value: B) -> Either[A, B]: ...


@inductive
class Decision[P: Type]:
    @constructor
    def Yes(proof: P) -> Decision[P]: ...
    @constructor
    def No(refutation: Not(P)) -> Decision[P]: ...


@dependent
def decision_weight[P: Type](d: Decision[P]) -> Nat:
    match d:
        case Yes(p):
            return 1
        case No(np):
            return 0


@dependent(decreases="d")
def weight_yes[P: Type](d: Decision[P], p: P) -> Eq[Nat, decision_weight(d), 1]:
    match d:
        case Yes(q):
            return refl(1)
        case No(np):
            return absurd(Eq[Nat, 0, 1], np(p))


@dependent(decreases="d")
def weight_no[P: Type](d: Decision[P], np: Not(P)) -> Eq[Nat, decision_weight(d), 0]:
    match d:
        case Yes(p):
            return absurd(Eq[Nat, 1, 0], np(p))
        case No(nq):
            return refl(0)


@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...


@dependent(decreases="xs")
def length[A: Type](xs: List[A]) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return S(length(tail))


@dependent(decreases="xs", motive_level=1)
def Has[A: Type](x: A, xs: List[A]) -> Type:
    match xs:
        case Nil():
            return Empty
        case Cons(y, tail):
            return Either[Eq[A, x, y], Has(x, tail)]


@dependent(decreases="xs", motive_level=1)
def NoDup[A: Type](xs: List[A]) -> Type:
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[Not(Has(x, tail)), lambda _: NoDup(tail)]


@dependent(decreases="xs")
def count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return add(decision_weight(dec(x)), count(dec, tail))


@dependent
def reject_head[A: Type, P: Type](x: A, d: Decision[P], tail: List[A]) -> List[A]:
    match d:
        case Yes(p):
            return tail
        case No(np):
            return Cons(x, tail)


@dependent(decreases="xs")
def reject[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> List[A]:
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(x, tail):
            return reject_head(x, dec(x), reject(dec, tail))


@dependent(decreases="xs")
def map[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> List[B]:
    match xs:
        case Nil():
            return Nil[B]()
        case Cons(x, tail):
            return Cons(f(x), map(f, tail))


@dependent
def either_elim[A: Type, B: Type, C: Type](
    value: Either[A, B], left: Pi[A, lambda _: C], right: Pi[B, lambda _: C]
) -> C:
    return induct(0, value, lambda _: C, lambda x: left(x), lambda y: right(y))


@inductive
class Removal[A: Type, x: A]:
    source: Index[List[A]]
    rest: Index[List[A]]

    @constructor
    def RemoveHere(tail: List[A]) -> Removal[A, x, Cons(x, tail), tail]: ...
    @constructor
    def RemoveThere(
        head: A, ys: List[A], zs: List[A], step: Removal[A, x, ys, zs]
    ) -> Removal[A, x, Cons(head, ys), Cons(head, zs)]: ...


@theorem(decreases="xs")
def find_removal[A: Type](
    x: A, xs: List[A], member: Has(x, xs)
) -> Sigma[List[A], lambda rest: Removal[A, x, xs, rest]]:
    match xs:
        case Nil():
            return absurd(Sigma[List[A], lambda rest: Removal[A, x, Nil[A](), rest]], member)
        case Cons(y, tail):
            match member:
                case Left(eq):
                    return transport[A, x, y](
                        lambda z: Sigma[List[A], lambda rest: Removal[A, x, Cons(z, tail), rest]],
                        eq,
                        Pair(tail, RemoveHere[A, x](tail)),
                    )
                case Right(later):
                    found = find_removal(x, tail, later)
                    return Pair(
                        Cons(y, found.fst), RemoveThere[A, x](y, tail, found.fst, found.snd)
                    )


@theorem(decreases="r")
def removal_present[A: Type, x: A, ys: List[A], zs: List[A]](r: Removal[A, x, ys, zs]) -> Has(
    x, ys
):
    match r:
        case RemoveHere(tail):
            return Left(refl(x))
        case RemoveThere(head, before, after, step):
            return Right(removal_present(step))


@theorem(decreases="r")
def removal_include[A: Type, x: A, ys: List[A], zs: List[A]](
    q: A, r: Removal[A, x, ys, zs], member: Has(q, zs)
) -> Has(q, ys):
    match r:
        case RemoveHere(tail):
            return Right(member)
        case RemoveThere(head, before, after, step):
            return either_elim[Eq[A, q, head], Has(q, after), Has(q, Cons(head, before))](
                member, lambda eq: Left(eq), lambda later: Right(removal_include(q, step, later))
            )


@theorem(decreases="r")
def removal_keep[A: Type, x: A, ys: List[A], zs: List[A]](
    q: A, r: Removal[A, x, ys, zs], member: Has(q, ys), distinct: Not(Eq[A, q, x])
) -> Has(q, zs):
    match r:
        case RemoveHere(tail):
            return either_elim(
                member, lambda eq: absurd(Has(q, tail), distinct(eq)), lambda later: later
            )
        case RemoveThere(head, before, after, step):
            return either_elim[Eq[A, q, head], Has(q, before), Has(q, Cons(head, after))](
                member,
                lambda eq: Left(eq),
                lambda later: Right(removal_keep(q, step, later, distinct)),
            )


@theorem(decreases="r")
def removal_nodup[A: Type, x: A, ys: List[A], zs: List[A]](
    r: Removal[A, x, ys, zs], unique: NoDup(ys)
) -> NoDup(zs):
    match r:
        case RemoveHere(tail):
            return unique.snd
        case RemoveThere(head, before, after, step):
            return Pair(
                lambda member: unique.fst(removal_include(head, step, member)),
                removal_nodup(step, unique.snd),
            )


@theorem(decreases="r")
def removal_absent[A: Type, x: A, ys: List[A], zs: List[A]](
    r: Removal[A, x, ys, zs], unique: NoDup(ys)
) -> Not(Has(x, zs)):
    match r:
        case RemoveHere(tail):
            return unique.fst
        case RemoveThere(head, before, after, step):
            return lambda member: either_elim[Eq[A, x, head], Has(x, after), Empty](
                member,
                lambda eq: unique.fst(
                    transport[A, x, head](lambda q: Has(q, before), eq, removal_present(step))
                ),
                lambda later: removal_absent(step, unique.snd)(later),
            )


@theorem(decreases="r")
def removal_count[A: Type, x: A, ys: List[A], zs: List[A], P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda q: Decision[P(q)]], r: Removal[A, x, ys, zs]
) -> Eq[Nat, count(dec, ys), add(decision_weight(dec(x)), count(dec, zs))]:
    match r:
        case RemoveHere(tail):
            return refl(add(decision_weight(dec(x)), count(dec, tail)))
        case RemoveThere(head, before, after, step):
            return trans(
                cong(lambda n: add(decision_weight(dec(head)), n), removal_count(dec, step)),
                add_swap(decision_weight(dec(head)), decision_weight(dec(x)), count(dec, after)),
            )


@theorem
def tail_forward[A: Type, x: A, tail: List[A], ys: List[A], zs: List[A]](
    r: Removal[A, x, ys, zs],
    unique: NoDup(Cons(x, tail)),
    forward: Pi[A, lambda q: Pi[Has(q, Cons(x, tail)), lambda _: Has(q, ys)]],
    q: A,
    member: Has(q, tail),
) -> Has(q, zs):
    return removal_keep(
        q,
        r,
        forward(q)(Right(member)),
        lambda eq: unique.fst(transport[A, q, x](lambda z: Has(z, tail), eq, member)),
    )


@theorem
def tail_backward[A: Type, x: A, tail: List[A], ys: List[A], zs: List[A]](
    r: Removal[A, x, ys, zs],
    unique: NoDup(ys),
    backward: Pi[A, lambda q: Pi[Has(q, ys), lambda _: Has(q, Cons(x, tail))]],
    q: A,
    member: Has(q, zs),
) -> Has(q, tail):
    return either_elim[Eq[A, q, x], Has(q, tail), Has(q, tail)](
        backward(q)(removal_include(q, r, member)),
        lambda eq: absurd(
            Has(q, tail),
            removal_absent(r, unique)(transport[A, q, x](lambda z: Has(z, zs), eq, member)),
        ),
        lambda later: later,
    )


@dependent
def SameCountAt[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> Type:
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
                        lambda backward: Eq[Nat, count(dec, xs), count(dec, ys)],
                    ],
                ],
            ],
        ],
    ]


@theorem(decreases="ys")
def same_count_nil[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]],
    ys: List[A],
    backward: Pi[A, lambda x: Pi[Has(x, ys), lambda _: Empty]],
) -> Eq[Nat, 0, count(dec, ys)]:
    match ys:
        case Nil():
            return refl(0)
        case Cons(y, tail):
            return absurd(Eq[Nat, 0, count(dec, Cons(y, tail))], backward(y)(Left(refl(y))))


@theorem
def same_count_step[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]],
    x: A,
    tail: List[A],
    ih: SameCountAt(dec, tail),
    ys: List[A],
    ux: NoDup(Cons(x, tail)),
    uy: NoDup(ys),
    forward: Pi[A, lambda q: Pi[Has(q, Cons(x, tail)), lambda _: Has(q, ys)]],
    backward: Pi[A, lambda q: Pi[Has(q, ys), lambda _: Has(q, Cons(x, tail))]],
) -> Eq[Nat, count(dec, Cons(x, tail)), count(dec, ys)]:
    found = find_removal(x, ys, forward(x)(Left(refl(x))))
    rest = found.fst
    removal = found.snd
    proof = ih(rest)(ux.snd)(removal_nodup(removal, uy))(
        lambda q: lambda member: tail_forward(removal, ux, forward, q, member)
    )(lambda q: lambda member: tail_backward(removal, uy, backward, q, member))
    return trans(
        cong(lambda n: add(decision_weight(dec(x)), n), proof), sym(removal_count(dec, removal))
    )


@theorem
def same_count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> SameCountAt(dec, xs):
    return induct(
        0,
        xs,
        lambda zs: SameCountAt(dec, zs),
        lambda ys: (
            lambda ux: lambda uy: lambda forward: lambda backward: same_count_nil(dec, ys, backward)
        ),
        lambda x, tail, ih: (
            lambda ys: (
                lambda ux: (
                    lambda uy: (
                        lambda forward: (
                            lambda backward: same_count_step(
                                dec, x, tail, ih, ys, ux, uy, forward, backward
                            )
                        )
                    )
                )
            )
        ),
    )


@theorem(decreases="xs")
def map_has[A: Type, B: Type](f: Pi[A, lambda _: B], x: A, xs: List[A], member: Has(x, xs)) -> Has(
    f(x), map(f, xs)
):
    match xs:
        case Nil():
            return absurd(Has(f(x), Nil[B]()), member)
        case Cons(y, tail):
            return either_elim[Eq[A, x, y], Has(x, tail), Has(f(x), Cons(f(y), map(f, tail)))](
                member,
                lambda eq: Left(cong(f, eq)),
                lambda later: Right(map_has(f, x, tail, later)),
            )


@theorem(decreases="xs")
def map_injective_has[A: Type, B: Type](
    f: Pi[A, lambda _: B],
    injective: Pi[A, lambda x: Pi[A, lambda y: Pi[Eq[B, f(x), f(y)], lambda _: Eq[A, x, y]]]],
    x: A,
    xs: List[A],
    member: Has(f(x), map(f, xs)),
) -> Has(x, xs):
    match xs:
        case Nil():
            return absurd(Has(x, Nil[A]()), member)
        case Cons(y, tail):
            return either_elim[Eq[B, f(x), f(y)], Has(f(x), map(f, tail)), Has(x, Cons(y, tail))](
                member,
                lambda eq: Left(injective(x)(y)(eq)),
                lambda later: Right(map_injective_has(f, injective, x, tail, later)),
            )


@theorem(decreases="xs")
def map_nodup[A: Type, B: Type](
    f: Pi[A, lambda _: B],
    injective: Pi[A, lambda x: Pi[A, lambda y: Pi[Eq[B, f(x), f(y)], lambda _: Eq[A, x, y]]]],
    xs: List[A],
    unique: NoDup(xs),
) -> NoDup(map(f, xs)):
    match xs:
        case Nil():
            return Unit_()
        case Cons(x, tail):
            return Pair(
                lambda member: unique.fst(map_injective_has(f, injective, x, tail, member)),
                map_nodup(f, injective, tail, unique.snd),
            )


@theorem
def inverse_injective[A: Type](
    f: Pi[A, lambda _: A],
    back: Pi[A, lambda _: A],
    inverse: Pi[A, lambda x: Eq[A, back(f(x)), x]],
    x: A,
    y: A,
    eq: Eq[A, f(x), f(y)],
) -> Eq[A, x, y]:
    return trans(sym(inverse(x)), trans(cong(back, eq), inverse(y)))


@record
class Enumeration[A: Type]:
    r"""A duplicate-free complete enumeration of a finite carrier ``A``.

    :ivar elements: The concrete list containing every element of ``A``.
    :ivar unique: Evidence that ``elements`` has no duplicates.
    :ivar complete: Membership evidence for every value ``x : A``.
    """
    elements: List[A]
    unique: NoDup(self.elements)
    complete: Pi[A, lambda x: Has(x, self.elements)]


@theorem
def bijection_count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]],
    f: Pi[A, lambda _: A],
    back: Pi[A, lambda _: A],
    left_inverse: Pi[A, lambda x: Eq[A, back(f(x)), x]],
    right_inverse: Pi[A, lambda x: Eq[A, f(back(x)), x]],
    finite: Enumeration[A],
) -> Eq[Nat, count(dec, map(f, finite.elements)), count(dec, finite.elements)]:
    return same_count(dec, map(f, finite.elements))(finite.elements)(
        map_nodup(
            f,
            lambda x: lambda y: lambda eq: inverse_injective(f, back, left_inverse, x, y, eq),
            finite.elements,
            finite.unique,
        )
    )(finite.unique)(lambda x: lambda member: finite.complete(x))(
        lambda x: (
            lambda member: transport[A, f(back(x)), x](
                lambda q: Has(q, map(f, finite.elements)),
                right_inverse(x),
                map_has(f, back(x), finite.elements, finite.complete(back(x))),
            )
        )
    )


@theorem(decreases="xs")
def count_map[A: Type, B: Type, P: Pi[B, lambda _: Type], Q: Pi[A, lambda _: Type]](
    dp: Pi[B, lambda x: Decision[P(x)]],
    dq: Pi[A, lambda x: Decision[Q(x)]],
    f: Pi[A, lambda _: B],
    weights: Pi[A, lambda x: Eq[Nat, decision_weight(dp(f(x))), decision_weight(dq(x))]],
    xs: List[A],
) -> Eq[Nat, count(dp, map(f, xs)), count(dq, xs)]:
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(
                cong(lambda n: add(n, count(dp, map(f, tail))), weights(x)),
                cong(lambda n: add(decision_weight(dq(x)), n), count_map(dp, dq, f, weights, tail)),
            )


@theorem(decreases="left")
def weight_unique[P: Type](
    left: Decision[P], right: Decision[P]
) -> Eq[Nat, decision_weight(left), decision_weight(right)]:
    match left:
        case Yes(p):
            return sym(weight_yes(right, p))
        case No(np):
            return sym(weight_no(right, np))


@theorem
def weight_transport[A: Type, P: Pi[A, lambda _: Type], x: A, y: A](
    eq: Eq[A, x, y], dx: Decision[P(x)], dy: Decision[P(y)]
) -> Eq[Nat, decision_weight(dx), decision_weight(dy)]:
    return J(
        0,
        A,
        x,
        lambda end, _: Pi[
            Decision[P(end)], lambda d: Eq[Nat, decision_weight(dx), decision_weight(d)]
        ],
        lambda d: weight_unique(dx, d),
        y,
        eq,
    )(dy)


# Group laws are inputs to the theorem, not global axioms. The concrete
# instances below construct all of these proofs.
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
    return trans(
        sym(g.assoc(g.inverse(a))(a)(x)),
        trans(cong(lambda y: g.op(y)(x), g.left_inverse(a)), g.left_unit(x)),
    )


@theorem
def right_recover[A: Type](g: Group[A], a: A, x: A) -> Eq[A, g.op(a)(g.op(g.inverse(a))(x)), x]:
    return trans(
        sym(g.assoc(a)(g.inverse(a))(x)),
        trans(cong(lambda y: g.op(y)(x), g.right_inverse(a)), g.left_unit(x)),
    )


@dependent
def Related[A: Type](g: Group[A], h: Subgroup[A, g], a: A, b: A) -> Type:
    return h.member(g.op(g.inverse(a))(b))


@theorem
def related_refl[A: Type](g: Group[A], h: Subgroup[A, g], a: A) -> Related(g, h, a, a):
    return transport[A, g.unit, g.op(g.inverse(a))(a)](
        h.member, sym(g.left_inverse(a)), h.unit_closed
    )


@theorem
def related_witness[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A, x: A, px: h.member(x), eq: Eq[A, g.op(a)(x), b]
) -> Related(g, h, a, b):
    return transport[A, x, g.op(g.inverse(a))(b)](
        h.member, trans(sym(left_recover(g, a, x)), cong(lambda y: g.op(g.inverse(a))(y), eq)), px
    )


@theorem
def cancel_right_inverse[A: Type](
    g: Group[A], a: A, x: A
) -> Eq[A, g.op(g.op(a)(x))(g.inverse(x)), a]:
    return trans(
        g.assoc(a)(x)(g.inverse(x)),
        trans(cong(lambda y: g.op(a)(y), g.right_inverse(x)), g.right_unit(a)),
    )


@theorem
def related_sym[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A, p: Related(g, h, a, b)
) -> Related(g, h, b, a):
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
    match d:
        case Yes(p):
            return le_step(bound)
        case No(np):
            return LESucc(length(tail), n, bound)


@theorem(decreases="xs")
def reject_bound[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> LE[length(reject(dec, xs)), length(xs)]:
    match xs:
        case Nil():
            return LEZero(0)
        case Cons(x, tail):
            return reject_bound_head(
                x, dec(x), reject(dec, tail), length(tail), reject_bound(dec, tail)
            )


@theorem(decreases="d")
def split_head[A: Type, P: Type](
    x: A, d: Decision[P], rest: List[A], n: Nat
) -> Eq[
    Nat, add(add(decision_weight(d), n), length(reject_head(x, d, rest))), S(add(n, length(rest)))
]:
    match d:
        case Yes(p):
            return refl(S(add(n, length(rest))))
        case No(np):
            return add_succ(n, length(rest))


@theorem(decreases="xs")
def count_split[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> Eq[Nat, add(count(dec, xs), length(reject(dec, xs))), length(xs)]:
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(
                split_head(x, dec(x), reject(dec, tail), count(dec, tail)),
                cong(lambda n: S(n), count_split(dec, tail)),
            )


@theorem(decreases="d")
def reject_head_yes[A: Type, P: Type](
    x: A, d: Decision[P], rest: List[A], proof: P
) -> Eq[List[A], reject_head(x, d, rest), rest]:
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
    return count[A, R(a)](dec(a), xs)


@dependent
def Uniform[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    dec: Pi[A, lambda a: Pi[A, lambda b: Decision[R(a)(b)]]], h: Nat, xs: List[A]
) -> Type:
    return Pi[A, lambda a: Pi[Has(a, xs), lambda _: Eq[Nat, class_size(dec, a, xs), h]]]


@dependent
def Divisible(h: Nat, n: Nat) -> Type:
    # The witness is an actual natural number, together with its equality proof.
    return Sigma[Nat, lambda k: Eq[Nat, n, mul(h, k)]]


@theorem
def class_disjoint[A: Type, R: Pi[A, lambda a: Pi[A, lambda b: Type]]](
    laws: Equivalence[A, R], a: A, b: A, distinct: Not(R(a)(b)), x: A, p: R(b)(x)
) -> Not(R(a)(x)):
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
    return partition_fuel(dec, laws, h, length(xs))(xs)(le_refl(length(xs)))(uniform)


# Every hypothesis below is group structure, a decidable subgroup, or an
# exhaustive duplicate-free enumeration. No coset partition is supplied.
@theorem
def coset_equivalence[A: Type](
    g: Group[A], h: Subgroup[A, g]
) -> Equivalence[A, lambda a: lambda b: Related(g, h, a, b)]:
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
    return uniform_partition(dec, laws, h, xs, lambda a: lambda member: sizes(a))


@dependent
def coset_decide[A: Type](
    g: Group[A], h: Subgroup[A, g], a: A, b: A
) -> Decision[Related(g, h, a, b)]:
    return h.decide(g.op(g.inverse(a))(b))


@theorem
def lagrange[A: Type](
    g: Group[A],
    h: Subgroup[A, g],
    finite: Enumeration[A],
) -> Divisible(count(h.decide, finite.elements), length(finite.elements)):
    r"""Lagrange's theorem: :math:`|H| \mid |G|` for a finite group ``G`` and subgroup ``H``."""
    return enumeration_partition[A, lambda a: lambda b: Related(g, h, a, b)](
        lambda a: lambda b: coset_decide(g, h, a, b),
        coset_equivalence(g, h),
        count(h.decide, finite.elements),
        finite.elements,
        lambda a: coset_size(g, h, finite, a),
    )


# Concrete instances: the two-element group, with its trivial and whole
# subgroups. Both conclusions are applications of the general theorem.
@inductive
class Bit:
    @constructor
    def B0() -> Bit: ...
    @constructor
    def B1() -> Bit: ...


@dependent
def flip(x: Bit) -> Bit:
    match x:
        case B0():
            return B1()
        case B1():
            return B0()


@dependent
def xor(x: Bit, y: Bit) -> Bit:
    match x:
        case B0():
            return y
        case B1():
            return flip(y)


@theorem
def xor_assoc(x: Bit, y: Bit, z: Bit) -> Eq[Bit, xor(xor(x, y), z), xor(x, xor(y, z))]:
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
    match x:
        case B0():
            return refl(B0())
        case B1():
            return refl(B1())


@theorem
def xor_self(x: Bit) -> Eq[Bit, xor(x, x), B0()]:
    match x:
        case B0():
            return refl(B0())
        case B1():
            return refl(B0())


@dependent
def bit_group() -> Group[Bit]:
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
    match x:
        case B0():
            return Unit
        case B1():
            return Empty


@dependent
def zero_decide(x: Bit) -> Decision[IsZero(x)]:
    match x:
        case B0():
            return Yes(Unit_())
        case B1():
            return No(lambda p: p)


@theorem
def zero_closed(x: Bit, y: Bit, px: IsZero(x), py: IsZero(y)) -> IsZero(xor(x, y)):
    match x:
        case B0():
            return py
        case B1():
            return absurd(IsZero(xor(B1(), y)), px)


@dependent
def trivial_subgroup() -> Subgroup[Bit, bit_group()]:
    return Subgroup[Bit, bit_group()](
        lambda x: IsZero(x),
        lambda x: zero_decide(x),
        Unit_(),
        lambda x: lambda y: lambda px: lambda py: zero_closed(x, y, px, py),
        lambda x: lambda px: px,
    )


@dependent
def whole_subgroup() -> Subgroup[Bit, bit_group()]:
    return Subgroup[Bit, bit_group()](
        lambda x: Unit,
        lambda x: Yes(Unit_()),
        Unit_(),
        lambda x: lambda y: lambda px: lambda py: Unit_(),
        lambda x: lambda px: Unit_(),
    )


@theorem
def zero_not_one(p: Eq[Bit, B0(), B1()]) -> Empty:
    return transport[Bit, B0(), B1()](lambda x: IsZero(x), p, Unit_())


@dependent
def bit_elements() -> List[Bit]:
    return Cons(B0(), Cons(B1(), Nil()))


@theorem
def bit_complete(x: Bit) -> Has(x, bit_elements()):
    match x:
        case B0():
            return Left(refl(B0()))
        case B1():
            return Right(Left(refl(B1())))


@dependent
def bit_enumeration() -> Enumeration[Bit]:
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


@theorem
def lagrange_trivial_example() -> Divisible(1, 2):
    return lagrange(bit_group(), trivial_subgroup(), bit_enumeration())


@theorem
def lagrange_whole_example() -> Divisible(2, 2):
    return lagrange(bit_group(), whole_subgroup(), bit_enumeration())
