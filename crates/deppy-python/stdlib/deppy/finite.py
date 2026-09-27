from deppy._builtins import (
    dependent, theorem, inductive, constructor, record, Index, Type, Pi, Sigma,
    Pair, Nat, Eq, refl, J, induct, absurd,
)
from deppy.lists import (
    List, Nil, Cons, length, Mem, NoDup, All, Any, count, reject_head, reject,
    map, length_map, map_mem, map_nodup, map_mem_reflect as map_injective_has,
    all_decide, any_decide, all_get, all_intro, any_from_mem, any_witness,
    Removal, RemoveHere, RemoveThere, find_removal,
)
from deppy.data import (
    Empty, Unit, MkUnit, Not, Sum, Left, Right, Decidable, Yes, No,
    decision_weight, weight_yes, weight_no,
)
from deppy.equality import sym, trans, cong, transport
from deppy.tactics import rewrite, rewrite_in
from deppy.nat import add, add_swap
from deppy.functions import Bijection, bijection_injective

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
def finite_count[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decide: Pi[A, lambda x: Decidable[P(x)]]
) -> Nat:
    """Count the elements of a finite carrier satisfying a predicate."""
    return count(decide, finite.elements)


@dependent(decreases="decision")
def finite_all_from_decision[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decision: Decidable[All(P, finite.elements)]
) -> Decidable[Pi[A, lambda x: P(x)]]:
    match decision:
        case Yes(all):
            return Yes[Pi[A, lambda x: P(x)]](lambda x: all_get(P, x, finite.elements, finite.complete(x), all))
        case No(refute):
            return No[Pi[A, lambda x: P(x)]](lambda every: refute(all_intro(P, finite.elements, every)))


@dependent
def finite_all_decide[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decide: Pi[A, lambda x: Decidable[P(x)]]
) -> Decidable[Pi[A, lambda x: P(x)]]:
    """Decide a predicate for every element of a finite carrier."""
    return finite_all_from_decision(finite, all_decide(decide, finite.elements))


@dependent(decreases="decision")
def finite_any_from_decision[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decision: Decidable[Any(P, finite.elements)]
) -> Decidable[Sigma[A, lambda x: P(x)]]:
    match decision:
        case Yes(exists):
            return Yes[Sigma[A, lambda x: P(x)]](any_witness(P, finite.elements, exists))
        case No(refute):
            return No[Sigma[A, lambda x: P(x)]](lambda witness: refute(any_from_mem(
                P, witness.fst, finite.elements, finite.complete(witness.fst), witness.snd
            )))


@dependent
def finite_any_decide[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decide: Pi[A, lambda x: Decidable[P(x)]]
) -> Decidable[Sigma[A, lambda x: P(x)]]:
    """Decide existence and return an element when one satisfies the predicate."""
    return finite_any_from_decision(finite, any_decide(decide, finite.elements))


@dependent
def finite_search[A: Type, P: Pi[A, lambda _: Type]](
    finite: Enumeration[A], decide: Pi[A, lambda x: Decidable[P(x)]]
) -> Decidable[Sigma[A, lambda x: P(x)]]:
    """A finite search with a proved witness or a refutation."""
    return finite_any_decide(finite, decide)


@dependent
def bijection_enumeration[A: Type, B: Type](b: Bijection[A, B], finite: Enumeration[A]) -> Enumeration[B]:
    """Transport a complete duplicate-free enumeration along a bijection."""
    return Enumeration[B](
        map(b.forward, finite.elements),
        map_nodup(b.forward, lambda x: lambda y: lambda equal: bijection_injective(b, x, y, equal),
                  finite.elements, finite.unique),
        lambda y: transport[B, b.forward(b.backward(y)), y](
            lambda q: Mem(q, map(b.forward, finite.elements)), b.right_inverse(y),
            map_mem(b.forward, b.backward(y), finite.elements, finite.complete(b.backward(y))),
        ),
    )


@theorem
def bijection_cardinality[A: Type, B: Type](b: Bijection[A, B], finite: Enumeration[A]) -> Eq[
    Nat, length(bijection_enumeration(b, finite).elements), length(finite.elements)
]:
    """A bijection preserves the size of a finite carrier."""
    return length_map(b.forward, finite.elements)


@dependent
def either_elim[A: Type, B: Type, C: Type](
    value: Either[A, B], left: Pi[A, lambda _: C], right: Pi[B, lambda _: C]
) -> C:
    r"""Eliminate either alternative using the corresponding branch function."""
    return induct(0, value, lambda _: C, lambda x: left(x), lambda y: right(y))


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
