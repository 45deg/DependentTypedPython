from __future__ import annotations
from deppy._builtins import dependent, theorem, inductive, constructor, record, Index, Type, Pi, Sigma, Pair, Nat, Eq, refl, J, induct, absurd
from deppy.lists import List, Nil, Cons, length, Mem, NoDup, count, reject_head, reject, map
from deppy.data import Empty, Unit, MkUnit, Not, Sum, Left, Right, Decidable, Yes, No, decision_weight, weight_yes, weight_no
from deppy.equality import sym, trans, cong, transport
from deppy.tactics import rewrite, rewrite_in
from deppy.nat import add, add_swap

# Names retained for the finite proof examples while sharing the stdlib carriers.
from deppy.data import Sum as Either, Decidable as Decision, MkUnit as Unit_
from deppy.lists import Mem as Has


@record
class Enumeration[A: Type]:
    """A complete list of a finite carrier, with no repeated elements."""
    elements: List[A]
    unique: NoDup(self.elements)
    complete: Pi[A, lambda x: Mem(x, self.elements)]


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
