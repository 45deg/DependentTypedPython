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

# Shared finite enumeration, group, and finite-product definitions.
# All theorem bodies are checked; no additional axioms are introduced.

@inductive
class Empty:
    r"""The empty type, used to express a contradiction."""
    pass


@inductive
class Unit:
    r"""The inhabited singleton type, used for a proposition with no obligations."""
    @constructor
    def Unit_() -> Unit: ...


@dependent
def Not(P: Type) -> Type:
    r"""Express the negation of P as a function from P to Empty."""
    return Pi[P, lambda _: Empty]


@inductive
class Either[A: Type, B: Type]:
    r"""Evidence for one of two alternatives, with its chosen branch."""
    @constructor
    def Left(value: A) -> Either[A, B]: ...
    @constructor
    def Right(value: B) -> Either[A, B]: ...


@inductive
class Decision[P: Type]:
    r"""A constructive decision carrying either a proof or a refutation."""
    @constructor
    def Yes(proof: P) -> Decision[P]: ...
    @constructor
    def No(refutation: Not(P)) -> Decision[P]: ...


@dependent
def decision_weight[P: Type](d: Decision[P]) -> Nat:
    r"""Assign weight one to a positive decision and zero to a negative one."""
    match d:
        case Yes(p):
            return 1
        case No(np):
            return 0


@dependent(decreases="d")
def weight_yes[P: Type](d: Decision[P], p: P) -> Eq[Nat, decision_weight(d), 1]:
    r"""A decision for an inhabited proposition has weight one.

    Case analysis rules out the negative branch using the supplied proof.
    """
    match d:
        case Yes(q):
            return refl(1)
        case No(np):
            return absurd(Eq[Nat, 0, 1], np(p))


@dependent(decreases="d")
def weight_no[P: Type](d: Decision[P], np: Not(P)) -> Eq[Nat, decision_weight(d), 0]:
    r"""A decision for a refuted proposition has weight zero.

    Case analysis rules out the positive branch using the supplied refutation.
    """
    match d:
        case Yes(p):
            return absurd(Eq[Nat, 1, 0], np(p))
        case No(nq):
            return refl(0)


@inductive
class List[A: Type]:
    r"""A finite list; repeated elements are permitted."""
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...


@dependent(decreases="xs")
def length[A: Type](xs: List[A]) -> Nat:
    r"""Count the list entries by structural recursion."""
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return S(length(tail))


@dependent(decreases="xs", motive_level=1)
def Has[A: Type](x: A, xs: List[A]) -> Type:
    r"""Express list membership by equality with the head or membership in the tail."""
    match xs:
        case Nil():
            return Empty
        case Cons(y, tail):
            return Either[Eq[A, x, y], Has(x, tail)]


@dependent(decreases="xs", motive_level=1)
def NoDup[A: Type](xs: List[A]) -> Type:
    r"""Require each head to be absent from its tail, recursively."""
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[Not(Has(x, tail)), lambda _: NoDup(tail)]


@dependent(decreases="xs")
def count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> Nat:
    r"""Count entries satisfying the decidable predicate, including repetitions."""
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return add(decision_weight(dec(x)), count(dec, tail))


@dependent
def reject_head[A: Type, P: Type](x: A, d: Decision[P], tail: List[A]) -> List[A]:
    r"""Discard the head on a positive decision; otherwise prepend it to the tail."""
    match d:
        case Yes(p):
            return tail
        case No(np):
            return Cons(x, tail)


@dependent(decreases="xs")
def reject[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> List[A]:
    r"""Keep precisely the entries for which the predicate is refuted."""
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(x, tail):
            return reject_head(x, dec(x), reject(dec, tail))


@dependent(decreases="xs")
def map[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> List[B]:
    r"""Apply a function to every entry, preserving list order."""
    match xs:
        case Nil():
            return Nil[B]()
        case Cons(x, tail):
            return Cons(f(x), map(f, tail))


@dependent
def either_elim[A: Type, B: Type, C: Type](
    value: Either[A, B], left: Pi[A, lambda _: C], right: Pi[B, lambda _: C]
) -> C:
    r"""Eliminate either alternative using the corresponding branch function."""
    return induct(0, value, lambda _: C, lambda x: left(x), lambda y: right(y))


@inductive
class Removal[A: Type, x: A]:
    r"""Evidence that deleting one occurrence of x turns source into rest."""
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
    r"""Turn membership into a remainder list and a one-occurrence removal proof.

    Recurse through the membership evidence, transporting the head case along equality.
    """
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
    r"""Recover membership of the removed element in the original list.

    Induct on the removal evidence.
    """
    match r:
        case RemoveHere(tail):
            return Left(refl(x))
        case RemoveThere(head, before, after, step):
            return Right(removal_present(step))


@theorem(decreases="r")
def removal_include[A: Type, x: A, ys: List[A], zs: List[A]](
    q: A, r: Removal[A, x, ys, zs], member: Has(q, zs)
) -> Has(q, ys):
    r"""Lift membership in the remainder to membership in the original list.

    Induct on the removal evidence, restoring the deleted entry.
    """
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
    r"""Preserve membership of an element distinct from the removed element.

    The head case excludes equality with the removed entry.
    """
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
    r"""Deleting one occurrence preserves absence of duplicates.

    Lift tail membership back to the original list to reuse its refutation.
    """
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
    r"""Removing an entry from a duplicate-free list leaves it absent.

    Induct on the removal evidence and use the original head's absence proof.
    """
    match r:
        case RemoveHere(tail):
            return unique.fst
        case RemoveThere(head, before, after, step):
            return lambda member: either_elim[Eq[A, x, head], Has(x, after), Empty](
                member,
                lambda eq: unique.fst(rewrite_in(eq, removal_present(step))),
                lambda later: removal_absent(step, unique.snd)(later),
            )


@theorem(decreases="r")
def removal_count[A: Type, x: A, ys: List[A], zs: List[A], P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda q: Decision[P(q)]], r: Removal[A, x, ys, zs]
) -> Eq[Nat, count(dec, ys), add(decision_weight(dec(x)), count(dec, zs))]:
    r"""Split a count into the removed entry's weight and the remainder's count.

    Induct on removal and swap the two leading summands in the recursive case.
    """
    match r:
        case RemoveHere(tail):
            return refl(add(decision_weight(dec(x)), count(dec, tail)))
        case RemoveThere(head, before, after, step):
            return rewrite(
                removal_count(dec, step),
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
    r"""Restrict a membership map to the lists with their matching head removed.

    Duplicate-freeness ensures that a tail member differs from the removed head.
    """
    return removal_keep(
        q,
        r,
        forward(q)(Right(member)),
        lambda eq: unique.fst(rewrite_in(eq, member)),
    )


@theorem
def tail_backward[A: Type, x: A, tail: List[A], ys: List[A], zs: List[A]](
    r: Removal[A, x, ys, zs],
    unique: NoDup(ys),
    backward: Pi[A, lambda q: Pi[Has(q, ys), lambda _: Has(q, Cons(x, tail))]],
    q: A,
    member: Has(q, zs),
) -> Has(q, tail):
    r"""Map membership in the remainder back to the original tail.

    Absence of the removed head excludes the head alternative.
    """
    return either_elim[Eq[A, q, x], Has(q, tail), Has(q, tail)](
        backward(q)(removal_include(q, r, member)),
        lambda eq: absurd(
            Has(q, tail),
            removal_absent(r, unique)(rewrite_in(eq, member)),
        ),
        lambda later: later,
    )


@dependent
def SameCountAt[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> Type:
    r"""State count invariance against any duplicate-free list with the same members."""
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
    r"""A list whose every member yields a contradiction has count zero.

    A nonempty list supplies its head as the contradictory member.
    """
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
    r"""Prove the inductive step for count invariance under reordering.

    Remove the matching head, apply the tail hypothesis, and restore its weight.
    """
    found = find_removal(x, ys, forward(x)(Left(refl(x))))
    rest = found.fst
    removal = found.snd
    proof = ih(rest)(ux.snd)(removal_nodup(removal, uy))(
        lambda q: lambda member: tail_forward(removal, ux, forward, q, member)
    )(lambda q: lambda member: tail_backward(removal, uy, backward, q, member))
    return rewrite(proof, sym(removal_count(dec, removal)))


@theorem
def same_count[A: Type, P: Pi[A, lambda _: Type]](
    dec: Pi[A, lambda x: Decision[P(x)]], xs: List[A]
) -> SameCountAt(dec, xs):
    r"""Equal membership and no duplicates imply equal predicate counts.

    Induct on the first list, removing one matching entry from the second.
    """
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
    r"""Map a membership proof along the list's mapping function.

    Use congruence in the head case and recursion in the tail case.
    """
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
    r"""Reflect membership in a mapped list along an injective function.

    Injectivity recovers head equality; the tail case recurses.
    """
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
    r"""An injective map preserves duplicate-freeness.

    Reflect mapped membership to contradict the original head's absence.
    """
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
    r"""A function with a left inverse is injective.

    Apply the inverse to the equality and simplify both inverse composites.
    """
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
    r"""A bijection of a finite carrier preserves predicate counts over its enumeration.

    Its inverse supplies injectivity and completeness for the mapped enumeration.
    """
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
    r"""Equal pointwise decision weights give equal counts over a mapped list.

    Induct on the list and combine the head equality with the tail equality.
    """
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
    r"""Two decisions of the same proposition have equal weights.

    The first decision supplies the proof or refutation needed to fix the second weight.
    """
    match left:
        case Yes(p):
            return sym(weight_yes(right, p))
        case No(np):
            return sym(weight_no(right, np))


@theorem
def weight_transport[A: Type, P: Pi[A, lambda _: Type], x: A, y: A](
    eq: Eq[A, x, y], dx: Decision[P(x)], dy: Decision[P(y)]
) -> Eq[Nat, decision_weight(dx), decision_weight(dy)]:
    r"""Equal predicate arguments yield equal decision weights.

    Equality elimination reduces the claim to two decisions of the same proposition.
    """
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
