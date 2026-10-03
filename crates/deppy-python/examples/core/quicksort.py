"""Axiom-free quicksort over Nat, with a proof of nondecreasing order.

The structural recursion argument is a length bound. Its proof prevents a
nonempty input from reaching the zero-fuel branch. Sorted alone does not assert
that the output is a permutation; that stronger theorem is outside this example.
"""
from deppy import dependent, theorem, Type, Nat, Z, S, Pi, Sigma, Pair, Eq, refl, absurd
from deppy.data import Unit, MkUnit, Left, Right
from deppy.lists import List, Nil, Cons, length, append, Mem, All, all_get, filter, filter_mem, length_filter_le
from deppy.nat_order import LE, le_decide, lt_decide, le_refl, le_pred, le_trans, le_weaken


@dependent(decreases="xs", motive_level=1)
def Sorted(xs: List[Nat]) -> Type:
    # Every tail element is >= the head, and the tail is itself sorted.
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[All(lambda y: LE[x, y], tail), lambda _: Sorted(tail)]


@dependent
def lower(pivot: Nat, xs: List[Nat]) -> List[Nat]:
    # Keep x <= pivot here, including duplicates of the pivot.
    return filter[Nat, lambda x: LE[x, pivot]](lambda x: le_decide(x, pivot), xs)


@dependent
def upper(pivot: Nat, xs: List[Nat]) -> List[Nat]:
    # Keep x > pivot, so the two partitions do not overlap.
    return filter[Nat, lambda x: LE[S(pivot), x]](lambda x: lt_decide(pivot, x), xs)


@theorem
def lower_bound(k: Nat, pivot: Nat, tail: List[Nat], bound: LE[S(length(tail)), S(k)]) -> LE[length(lower(pivot, tail)), k]:
    # Filtering cannot increase tail length; cancel S from the parent bound.
    return le_trans(length_filter_le[Nat, lambda x: LE[x, pivot]](lambda x: le_decide(x, pivot), tail), k, le_pred(length(tail), k, bound))


@theorem
def upper_bound(k: Nat, pivot: Nat, tail: List[Nat], bound: LE[S(length(tail)), S(k)]) -> LE[length(upper(pivot, tail)), k]:
    # The same length argument bounds the strict upper partition.
    return le_trans(length_filter_le[Nat, lambda x: LE[S(pivot), x]](lambda x: lt_decide(pivot, x), tail), k, le_pred(length(tail), k, bound))


@dependent(decreases="xs")
def quicksort_zero(xs: List[Nat], bound: LE[length(xs), 0]) -> List[Nat]:
    # A zero length bound rules out a nonempty input; no elements are discarded.
    match xs:
        case Nil():
            return Nil[Nat]()
        case Cons(x, tail):
            return absurd(List[Nat], bound)


@dependent(decreases="xs")
def quicksort_step(k: Nat, xs: List[Nat], bound: LE[length(xs), S(k)],
                   smaller: Pi[List[Nat], lambda ys: Pi[LE[length(ys), k], lambda _: List[Nat]]]) -> List[Nat]:
    # Partition the tail, sort both parts, then join left ++ [pivot] ++ right.
    match xs:
        case Nil():
            return Nil[Nat]()
        case Cons(pivot, tail):
            left_bound = lower_bound(k, pivot, tail, bound)
            right_bound = upper_bound(k, pivot, tail, bound)
            return append(smaller(lower(pivot, tail))(left_bound), Cons(pivot, smaller(upper(pivot, tail))(right_bound)))


@dependent(decreases="fuel")
def quicksort_bounded(fuel: Nat, xs: List[Nat], bound: LE[length(xs), fuel]) -> List[Nat]:
    # Recurse on fuel because filtered lists are not direct substructures.
    match fuel:
        case Z():
            return quicksort_zero(xs, bound)
        case S(k):
            return quicksort_step(k, xs, bound, lambda ys: lambda proof: quicksort_bounded(k, ys, proof))


@dependent
def quicksort(xs: List[Nat]) -> List[Nat]:
    # Input length is enough fuel: each recursive level removes its pivot.
    return quicksort_bounded(length(xs), xs, le_refl(length(xs)))


@theorem(decreases="xs")
def all_from_members[P: Pi[Nat, lambda _: Type]](
    xs: List[Nat], every: Pi[Nat, lambda x: Pi[Mem(x, xs), lambda _: P(x)]]
) -> All(P, xs):
    # Build All(P, xs) from a proof of P for each member of xs.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return Pair(every(x)(Left(refl(x))),
                        all_from_members(tail, lambda y: lambda member: every(y)(Right(member))))


@theorem(decreases="xs")
def all_append[P: Pi[Nat, lambda _: Type]](
    xs: List[Nat], ys: List[Nat], left: All(P, xs), right: All(P, ys)
) -> All(P, append(xs, ys)):
    # Concatenating two lists preserves a property shared by all their elements.
    match xs:
        case Nil():
            return right
        case Cons(x, tail):
            return Pair(left.fst, all_append(tail, ys, left.snd, right))


@theorem(decreases="xs")
def all_le_trans(x: Nat, pivot: Nat, xs: List[Nat], first: LE[x, pivot], rest: All(lambda y: LE[pivot, y], xs)) -> All(lambda y: LE[x, y], xs):
    # If x <= pivot <= y, transitivity gives x <= y throughout the list.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(y, tail):
            return Pair(le_trans(first, y, rest.fst), all_le_trans(x, pivot, tail, first, rest.snd))


@theorem(decreases="xs")
def sorted_join(pivot: Nat, xs: List[Nat], ys: List[Nat], left: Sorted(xs), right: Sorted(ys),
                below: All(lambda x: LE[x, pivot], xs), above: All(lambda y: LE[pivot, y], ys)) -> Sorted(append(xs, Cons(pivot, ys))):
    # The pivot bounds both sorted parts, so their concatenation is sorted.
    match xs:
        case Nil():
            return Pair(above, right)
        case Cons(x, tail):
            return Pair(all_append[lambda y: LE[x, y]](tail, Cons(pivot, ys), left.fst,
                                   Pair(below.fst, all_le_trans(x, pivot, ys, below.fst, above))),
                        sorted_join(pivot, tail, ys, left.snd, right, below.snd, above))


@theorem(decreases="xs")
def quicksort_preserves_all_zero[P: Pi[Nat, lambda _: Type]](xs: List[Nat], bound: LE[length(xs), 0], properties: All(P, xs)) -> All(P, quicksort_bounded(0, xs, bound)):
    # Only the empty input is possible when fuel is zero.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return absurd(All(P, quicksort_bounded(0, xs, bound)), bound)


@theorem(decreases="xs")
def quicksort_preserves_all_step[P: Pi[Nat, lambda _: Type]](k: Nat, xs: List[Nat], bound: LE[length(xs), S(k)], properties: All(P, xs),
    smaller: Pi[List[Nat], lambda ys: Pi[LE[length(ys), k], lambda b: Pi[All(P, ys), lambda _: All(P, quicksort_bounded(k, ys, b))]]]) -> All(P, quicksort_bounded(S(k), xs, bound)):
    # Filter membership recovers the input property; recursive sorting preserves it.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(pivot, tail):
            left_bound = lower_bound(k, pivot, tail, bound)
            right_bound = upper_bound(k, pivot, tail, bound)
            left_properties = all_from_members[P](lower(pivot, tail), lambda x: lambda member:
                all_get(P, x, tail, filter_mem[Nat, lambda y: LE[y, pivot]](lambda y: le_decide(y, pivot), x, tail, member).fst, properties.snd))
            right_properties = all_from_members[P](upper(pivot, tail), lambda x: lambda member:
                all_get(P, x, tail, filter_mem[Nat, lambda y: LE[S(pivot), y]](lambda y: lt_decide(pivot, y), x, tail, member).fst, properties.snd))
            return all_append[P](quicksort_bounded(k, lower(pivot, tail), left_bound),
                              Cons(pivot, quicksort_bounded(k, upper(pivot, tail), right_bound)),
                              smaller(lower(pivot, tail))(left_bound)(left_properties),
                              Pair(properties.fst, smaller(upper(pivot, tail))(right_bound)(right_properties)))


@theorem(decreases="fuel")
def quicksort_preserves_all[P: Pi[Nat, lambda _: Type]](fuel: Nat, xs: List[Nat], bound: LE[length(xs), fuel], properties: All(P, xs)) -> All(P, quicksort_bounded(fuel, xs, bound)):
    # Induct on fuel to preserve any universal element predicate P.
    match fuel:
        case Z():
            return quicksort_preserves_all_zero[P](xs, bound, properties)
        case S(k):
            return quicksort_preserves_all_step[P](k, xs, bound, properties, lambda ys: lambda proof: lambda props: quicksort_preserves_all(k, ys, proof, props))

@theorem(decreases="xs")
def quicksort_bounded_sorted_zero(xs: List[Nat], bound: LE[length(xs), 0]) -> Sorted(quicksort_bounded(0, xs, bound)):
    # The empty output is sorted; a nonempty input contradicts the length bound.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return absurd(Sorted(quicksort_bounded(0, xs, bound)), bound)


@theorem(decreases="xs")
def quicksort_bounded_sorted_step(k: Nat, xs: List[Nat], bound: LE[length(xs), S(k)],
    smaller: Pi[List[Nat], lambda ys: Pi[LE[length(ys), k], lambda b: Sorted(quicksort_bounded(k, ys, b))]]) -> Sorted(quicksort_bounded(S(k), xs, bound)):
    # Use recursive sortedness and preserved pivot bounds to apply sorted_join.
    match xs:
        case Nil():
            return MkUnit()
        case Cons(pivot, tail):
            left_bound = lower_bound(k, pivot, tail, bound)
            right_bound = upper_bound(k, pivot, tail, bound)
            below = all_from_members[lambda x: LE[x, pivot]](lower(pivot, tail), lambda x: lambda member:
                filter_mem[Nat, lambda y: LE[y, pivot]](lambda y: le_decide(y, pivot), x, tail, member).snd)
            above = all_from_members[lambda x: LE[pivot, x]](upper(pivot, tail), lambda x: lambda member:
                le_weaken(filter_mem[Nat, lambda y: LE[S(pivot), y]](lambda y: lt_decide(pivot, y), x, tail, member).snd))
            return sorted_join(pivot,
                quicksort_bounded(k, lower(pivot, tail), left_bound),
                quicksort_bounded(k, upper(pivot, tail), right_bound),
                smaller(lower(pivot, tail))(left_bound),
                smaller(upper(pivot, tail))(right_bound),
                quicksort_preserves_all[lambda x: LE[x, pivot]](k, lower(pivot, tail), left_bound, below),
                quicksort_preserves_all[lambda x: LE[pivot, x]](k, upper(pivot, tail), right_bound, above))


@theorem(decreases="fuel")
def quicksort_bounded_sorted(fuel: Nat, xs: List[Nat], bound: LE[length(xs), fuel]) -> Sorted(quicksort_bounded(fuel, xs, bound)):
    # Induct on fuel, checking both the base case and partition step.
    match fuel:
        case Z():
            return quicksort_bounded_sorted_zero(xs, bound)
        case S(k):
            return quicksort_bounded_sorted_step(k, xs, bound, lambda ys: lambda proof: quicksort_bounded_sorted(k, ys, proof))

@theorem
def quicksort_sorted(xs: List[Nat]) -> Sorted(quicksort(xs)):
    # Main theorem: for every xs, quicksort(xs) is in nondecreasing order.
    return quicksort_bounded_sorted(length(xs), xs, le_refl(length(xs)))


@dependent
def duplicates_example() -> Eq[List[Nat], quicksort(Cons(2, Cons(0, Cons(1, Cons(2, Nil[Nat]()))))), Cons(0, Cons(1, Cons(2, Cons(2, Nil[Nat]()))))]:
    return refl(Cons(0, Cons(1, Cons(2, Cons(2, Nil[Nat]())))))


@dependent
def empty_example() -> Eq[List[Nat], quicksort(Nil[Nat]()), Nil[Nat]()]:
    return refl(Nil[Nat]())


@dependent
def singleton_example() -> Eq[List[Nat], quicksort(Cons(3, Nil[Nat]())), Cons(3, Nil[Nat]())]:
    return refl(Cons(3, Nil[Nat]()))


@dependent
def descending_example() -> Eq[List[Nat], quicksort(Cons(3, Cons(2, Cons(1, Nil[Nat]())))), Cons(1, Cons(2, Cons(3, Nil[Nat]())))]:
    return refl(Cons(1, Cons(2, Cons(3, Nil[Nat]()))))


@dependent
def ordered_example() -> Eq[List[Nat], quicksort(Cons(0, Cons(1, Cons(2, Nil[Nat]())))), Cons(0, Cons(1, Cons(2, Nil[Nat]())))]:
    return refl(Cons(0, Cons(1, Cons(2, Nil[Nat]()))))


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    def to_list(xs):
        values = []
        while isinstance(xs, Cons):
            values.append(int(xs.head))
            xs = xs.tail
        return values

    for values in ([], [3], [3, 2, 1], [0, 1, 2], [2, 0, 1, 2]):
        xs = Nil[Nat]()
        for value in reversed(values):
            xs = Cons(value, xs)
        print(f"quicksort({values}) = {to_list(quicksort(xs))}")
