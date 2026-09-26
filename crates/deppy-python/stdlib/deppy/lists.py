from __future__ import annotations
from deppy._builtins import inductive, constructor, Index, dependent, theorem, Type, Pi, Sigma, Pair, Nat, Z, S, Eq, refl, absurd
from deppy.equality import cong, trans, sym, transport
from deppy.data import Empty, Unit, MkUnit, Sum, Left, Right, Not, Decidable, Yes, No, sum_elim, decide_and, decide_or, decision_weight
from deppy.nat import add, add_succ
from deppy.nat_order import LE, LEZero, LESucc, le_step


@inductive
class List[A: Type]:
    r"""A finite list of values of type ``A``.

    ``Nil`` is empty. ``Cons.head`` is the first value and ``Cons.tail`` is
    the remaining list.
    """
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...


@dependent(decreases="xs")
def length[A: Type](xs: List[A]) -> Nat:
    r"""Return the number :math:`|xs|` of elements in ``xs``."""
    match xs:
        case Nil():
            return 0
        case Cons(_, tail):
            return S(length(tail))


@dependent(decreases="xs", motive_level=1)
def Mem[A: Type](x: A, xs: List[A]) -> Type:
    r"""Membership proposition :math:`x \in xs`."""
    match xs:
        case Nil():
            return Empty
        case Cons(y, tail):
            return Sum[Eq[A, x, y], Mem(x, tail)]


@dependent(decreases="xs", motive_level=1)
def NoDup[A: Type](xs: List[A]) -> Type:
    r"""Proposition that ``xs`` contains no duplicate elements."""
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[Not(Mem(x, tail)), lambda _: NoDup(tail)]


@dependent(decreases="xs", motive_level=1)
def All[A: Type](P: Pi[A, lambda _: Type], xs: List[A]) -> Type:
    r"""Universal list predicate :math:`\forall x \in xs, P(x)`."""
    match xs:
        case Nil():
            return Unit
        case Cons(x, tail):
            return Sigma[P(x), lambda _: All(P, tail)]


@dependent(decreases="xs", motive_level=1)
def Any[A: Type](P: Pi[A, lambda _: Type], xs: List[A]) -> Type:
    r"""Existential list predicate :math:`\exists x \in xs, P(x)`."""
    match xs:
        case Nil():
            return Empty
        case Cons(x, tail):
            return Sum[P(x), Any(P, tail)]


@theorem(decreases="xs")
def all_get[A: Type](P: Pi[A, lambda _: Type], q: A, xs: List[A], member: Mem(q, xs), all: All(P, xs)) -> P(q):
    """A member of a list satisfying All has the requested property."""
    match xs:
        case Nil():
            return absurd(P(q), member)
        case Cons(x, tail):
            return sum_elim[Eq[A, q, x], Mem(q, tail), P(q)](
                member,
                lambda equal: transport[A, x, q](P, sym(equal), all.fst),
                lambda later: all_get(P, q, tail, later, all.snd),
            )


@theorem(decreases="xs")
def all_intro[A: Type](P: Pi[A, lambda _: Type], xs: List[A], every: Pi[A, lambda x: P(x)]) -> All(P, xs):
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return Pair(every(x), all_intro(P, tail, every))


@theorem(decreases="xs")
def any_from_mem[A: Type](P: Pi[A, lambda _: Type], q: A, xs: List[A], member: Mem(q, xs), proof: P(q)) -> Any(P, xs):
    match xs:
        case Nil():
            return absurd(Any(P, Nil[A]()), member)
        case Cons(x, tail):
            return sum_elim[Eq[A, q, x], Mem(q, tail), Any(P, Cons(x, tail))](
                member,
                lambda equal: Left(transport[A, q, x](P, equal, proof)),
                lambda later: Right(any_from_mem(P, q, tail, later, proof)),
            )


@dependent(decreases="xs")
def any_witness[A: Type](P: Pi[A, lambda _: Type], xs: List[A], exists: Any(P, xs)) -> Sigma[A, lambda x: P(x)]:
    match xs:
        case Nil():
            return absurd(Sigma[A, lambda x: P(x)], exists)
        case Cons(x, tail):
            return sum_elim[P(x), Any(P, tail), Sigma[A, lambda q: P(q)]](
                exists, lambda proof: Pair(x, proof), lambda later: any_witness(P, tail, later)
            )


@dependent(decreases="xs")
def all_decide[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Decidable[All(P, xs)]:
    """Decide whether every list element satisfies a predicate."""
    match xs:
        case Nil():
            return Yes(MkUnit())
        case Cons(x, tail):
            return decide_and(decide(x), all_decide(decide, tail))


@dependent(decreases="xs")
def any_decide[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Decidable[Any(P, xs)]:
    """Decide whether some list element satisfies a predicate."""
    match xs:
        case Nil():
            return No[Empty](lambda impossible: impossible)
        case Cons(x, tail):
            return decide_or(decide(x), any_decide(decide, tail))


@dependent
def search[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Decidable[Any(P, xs)]:
    """Search a list, returning either an existential proof or its refutation."""
    return any_decide(decide, xs)


@dependent(decreases="xs")
def append[A: Type](xs: List[A], ys: List[A]) -> List[A]:
    r"""Concatenate ``xs`` and ``ys``."""
    match xs:
        case Nil():
            return ys
        case Cons(h, t):
            return Cons(h, append(t, ys))


@theorem(decreases="xs")
def mem_append_left[A: Type](x: A, xs: List[A], ys: List[A], member: Mem(x, xs)) -> Mem(x, append(xs, ys)):
    """Membership in the left list is preserved by concatenation."""
    match xs:
        case Nil():
            return absurd(Mem(x, append(Nil[A](), ys)), member)
        case Cons(h, tail):
            return sum_elim[Eq[A, x, h], Mem(x, tail), Mem(x, append(Cons(h, tail), ys))](
                member, lambda eq: Left(eq), lambda later: Right(mem_append_left(x, tail, ys, later))
            )


@theorem(decreases="xs")
def mem_append_right[A: Type](x: A, xs: List[A], ys: List[A], member: Mem(x, ys)) -> Mem(x, append(xs, ys)):
    """Membership in the right list is preserved by concatenation."""
    match xs:
        case Nil():
            return member
        case Cons(h, tail):
            return Right(mem_append_right(x, tail, ys, member))


@theorem(decreases="xs")
def mem_append_cases[A: Type](x: A, xs: List[A], ys: List[A], member: Mem(x, append(xs, ys))) -> Sum[Mem(x, xs), Mem(x, ys)]:
    """An element of a concatenation belongs to one of its inputs."""
    match xs:
        case Nil():
            return Right(member)
        case Cons(h, tail):
            return sum_elim[Eq[A, x, h], Mem(x, append(tail, ys)), Sum[Mem(x, Cons(h, tail)), Mem(x, ys)]](
                member,
                lambda eq: Left(Left(eq)),
                lambda later: sum_elim[Mem(x, tail), Mem(x, ys), Sum[Mem(x, Cons(h, tail)), Mem(x, ys)]](
                    mem_append_cases(x, tail, ys, later),
                    lambda left: Left(Right(left)),
                    lambda right: Right(right),
                ),
            )


@dependent(decreases="xs")
def map[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> List[B]:
    r"""Apply ``f`` to every element of ``xs``."""
    match xs:
        case Nil():
            return Nil[B]()
        case Cons(h, t):
            return Cons(f(h), map(f, t))


@dependent(decreases="xs")
def append_assoc[A: Type](xs: List[A], ys: List[A], zs: List[A]) -> Eq[List[A], append(append(xs, ys), zs), append(xs, append(ys, zs))]:
    r"""Theorem ``append_assoc``: :math:`(xs {+\!+} ys) {+\!+} zs = xs {+\!+} (ys {+\!+} zs)`."""
    match xs:
        case Nil():
            return refl(append(ys, zs))
        case Cons(h, t):
            return cong(lambda rest: Cons(h, rest), append_assoc(t, ys, zs))


@dependent(decreases="xs")
def map_identity[A: Type](xs: List[A]) -> Eq[List[A], map(lambda x: x, xs), xs]:
    r"""Theorem ``map_identity``: mapping the identity function preserves a list."""
    match xs:
        case Nil():
            return refl(Nil[A]())
        case Cons(h, t):
            return cong(lambda rest: Cons(h, rest), map_identity(t))


@dependent(decreases="xs")
def map_composition[A: Type, B: Type, C: Type](f: Pi[A, lambda _: B], g: Pi[B, lambda _: C], xs: List[A]) -> Eq[List[C], map(g, map(f, xs)), map(lambda x: g(f(x)), xs)]:
    r"""Theorem ``map_composition``: :math:`map(g,map(f,xs))=map(g\circ f,xs)`."""
    match xs:
        case Nil():
            return refl(Nil[C]())
        case Cons(h, t):
            return cong(lambda rest: Cons(g(f(h)), rest), map_composition(f, g, t))


@theorem(decreases="xs")
def length_append[A: Type](xs: List[A], ys: List[A]) -> Eq[Nat, length(append(xs, ys)), add(length(xs), length(ys))]:
    """The length of a concatenation is the sum of its lengths."""
    match xs:
        case Nil():
            return refl(length(ys))
        case Cons(_, tail):
            return cong(lambda n: S(n), length_append(tail, ys))


@theorem(decreases="xs")
def length_map[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> Eq[Nat, length(map(f, xs)), length(xs)]:
    """Mapping preserves the number of elements."""
    match xs:
        case Nil():
            return refl(0)
        case Cons(_, tail):
            return cong(lambda n: S(n), length_map(f, tail))


@theorem(decreases="xs")
def map_append[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A], ys: List[A]) -> Eq[List[B], map(f, append(xs, ys)), append(map(f, xs), map(f, ys))]:
    """Mapping distributes over concatenation."""
    match xs:
        case Nil():
            return refl(map(f, ys))
        case Cons(x, tail):
            return cong(lambda rest: Cons(f(x), rest), map_append(f, tail, ys))


@dependent(decreases="xs")
def snoc[A: Type](xs: List[A], x: A) -> List[A]:
    r"""Append the single element ``x`` to the end of ``xs``."""
    match xs:
        case Nil():
            return Cons(x, Nil[A]())
        case Cons(h, t):
            return Cons(h, snoc(t, x))


@dependent(decreases="xs")
def reverse[A: Type](xs: List[A]) -> List[A]:
    r"""Reverse the order of a finite list."""
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(h, t):
            return snoc(reverse(t), h)


@theorem(decreases="xs")
def snoc_append[A: Type](xs: List[A], ys: List[A], x: A) -> Eq[
    List[A], snoc(append(xs, ys), x), append(xs, snoc(ys, x))
]:
    match xs:
        case Nil():
            return refl(snoc(ys, x))
        case Cons(h, tail):
            return cong(lambda rest: Cons(h, rest), snoc_append(tail, ys, x))


@theorem(decreases="xs")
def append_right_nil[A: Type](xs: List[A]) -> Eq[List[A], append(xs, Nil[A]()), xs]:
    match xs:
        case Nil():
            return refl(Nil[A]())
        case Cons(x, tail):
            return cong(lambda rest: Cons(x, rest), append_right_nil(tail))


@theorem(decreases="xs")
def reverse_append[A: Type](xs: List[A], ys: List[A]) -> Eq[
    List[A], reverse(append(xs, ys)), append(reverse(ys), reverse(xs))
]:
    """Reversing a concatenation reverses each part and swaps their order."""
    match xs:
        case Nil():
            return sym(append_right_nil(reverse(ys)))
        case Cons(x, tail):
            return trans(
                cong[List[A], List[A]](lambda rest: snoc(rest, x), reverse_append(tail, ys)),
                snoc_append(reverse(ys), reverse(tail), x),
            )


@theorem(decreases="xs")
def map_snoc[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A], x: A) -> Eq[
    List[B], map(f, snoc(xs, x)), snoc(map(f, xs), f(x))
]:
    match xs:
        case Nil():
            return refl(Cons(f(x), Nil[B]()))
        case Cons(h, tail):
            return cong(lambda rest: Cons(f(h), rest), map_snoc(f, tail, x))


@theorem(decreases="xs")
def map_reverse[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> Eq[
    List[B], map(f, reverse(xs)), reverse(map(f, xs))
]:
    """Mapping commutes with list reversal."""
    match xs:
        case Nil():
            return refl(Nil[B]())
        case Cons(x, tail):
            return trans(
                map_snoc(f, reverse(tail), x),
                cong[List[B], List[B]](lambda rest: snoc(rest, f(x)), map_reverse(f, tail)),
            )


@theorem(decreases="xs")
def length_snoc[A: Type](xs: List[A], x: A) -> Eq[Nat, length(snoc(xs, x)), S(length(xs))]:
    match xs:
        case Nil():
            return refl(1)
        case Cons(_, tail):
            return cong(lambda n: S(n), length_snoc(tail, x))


@theorem(decreases="xs")
def length_reverse[A: Type](xs: List[A]) -> Eq[Nat, length(reverse(xs)), length(xs)]:
    """Reversal preserves length."""
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(length_snoc(reverse(tail), x), cong(lambda n: S(n), length_reverse(tail)))


@dependent(decreases="xs")
def reverse_snoc[A: Type](xs: List[A], x: A) -> Eq[List[A], reverse(snoc(xs, x)), Cons(x, reverse(xs))]:
    r"""Theorem ``reverse_snoc``: reversing a final element moves it to the front."""
    match xs:
        case Nil():
            return refl(Cons(x, Nil[A]()))
        case Cons(h, t):
            return cong[List[A], List[A]](lambda rest: snoc(rest, h), reverse_snoc(t, x))


@dependent(decreases="xs")
def reverse_involution[A: Type](xs: List[A]) -> Eq[List[A], reverse(reverse(xs)), xs]:
    r"""Theorem ``reverse_involution``: :math:`reverse(reverse(xs))=xs`."""
    match xs:
        case Nil():
            return refl(Nil[A]())
        case Cons(h, t):
            return trans(reverse_snoc(reverse(t), h), cong(lambda rest: Cons(h, rest), reverse_involution(t)))


@dependent
def filter_head[A: Type, P: Type](x: A, d: Decidable[P], tail: List[A]) -> List[A]:
    match d:
        case Yes(_):
            return Cons(x, tail)
        case No(_):
            return tail


@dependent(decreases="xs")
def filter[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> List[A]:
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(x, tail):
            return filter_head(x, decide(x), filter(decide, tail))


@theorem(decreases="d")
def filter_mem_head[A: Type, P: Pi[A, lambda _: Type]](
    q: A, x: A, tail: List[A], kept: List[A], d: Decidable[P(x)],
    member: Mem(q, filter_head(x, d, kept)),
    reflect: Pi[Mem(q, kept), lambda _: Sigma[Mem(q, tail), lambda _: P(q)]],
) -> Sigma[Mem(q, Cons(x, tail)), lambda _: P(q)]:
    match d:
        case Yes(proof):
            return sum_elim[Eq[A, q, x], Mem(q, kept), Sigma[Mem(q, Cons(x, tail)), lambda _: P(q)]](
                member,
                lambda eq: Pair(Left(eq), transport[A, x, q](P, sym(eq), proof)),
                lambda later: Pair(Right(reflect(later).fst), reflect(later).snd),
            )
        case No(_):
            found = reflect(member)
            return Pair(Right(found.fst), found.snd)


@theorem(decreases="xs")
def filter_mem[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], q: A, xs: List[A], member: Mem(q, filter(decide, xs))
) -> Sigma[Mem(q, xs), lambda _: P(q)]:
    """Membership after filtering gives original membership and the predicate."""
    match xs:
        case Nil():
            return absurd(Sigma[Mem(q, Nil[A]()), lambda _: P(q)], member)
        case Cons(x, tail):
            return filter_mem_head(q, x, tail, filter(decide, tail), decide(x), member,
                                   lambda later: filter_mem(decide, q, tail, later))


@theorem(decreases="d")
def filter_head_mem_here[A: Type, P: Type](x: A, kept: List[A], d: Decidable[P], proof: P) -> Mem(
    x, filter_head(x, d, kept)
):
    match d:
        case Yes(_):
            return Left(refl(x))
        case No(refute):
            return absurd(Mem(x, filter_head(x, d, kept)), refute(proof))


@theorem(decreases="d")
def filter_head_mem_tail[A: Type, P: Type](q: A, x: A, kept: List[A], d: Decidable[P], member: Mem(q, kept)) -> Mem(
    q, filter_head(x, d, kept)
):
    match d:
        case Yes(_):
            return Right(member)
        case No(_):
            return member


@theorem(decreases="xs")
def filter_mem_intro[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], q: A, xs: List[A], member: Mem(q, xs), proof: P(q)
) -> Mem(q, filter(decide, xs)):
    """Original membership and a proof of the predicate give filtered membership."""
    match xs:
        case Nil():
            return absurd(Mem(q, filter(decide, Nil[A]())), member)
        case Cons(x, tail):
            return sum_elim[Eq[A, q, x], Mem(q, tail), Mem(q, filter(decide, Cons(x, tail)))](
                member,
                lambda eq: transport[A, x, q](
                    lambda z: Mem(z, filter(decide, Cons(x, tail))), sym(eq),
                    filter_head_mem_here(x, filter(decide, tail), decide(x), transport[A, q, x](P, eq, proof)),
                ),
                lambda later: filter_head_mem_tail(
                    q, x, filter(decide, tail), decide(x), filter_mem_intro(decide, q, tail, later, proof)
                ),
            )


@theorem(decreases="d")
def filter_nodup_head[A: Type, P: Pi[A, lambda _: Type]](
    x: A, tail: List[A], kept: List[A], d: Decidable[P(x)], unique: NoDup(Cons(x, tail)),
    kept_unique: NoDup(kept), reflect: Pi[Mem(x, kept), lambda _: Mem(x, tail)]
) -> NoDup(filter_head(x, d, kept)):
    match d:
        case Yes(_):
            return Pair(lambda member: unique.fst(reflect(member)), kept_unique)
        case No(_):
            return kept_unique


@theorem(decreases="xs")
def filter_nodup[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A], unique: NoDup(xs)
) -> NoDup(filter(decide, xs)):
    """Filtering preserves the absence of duplicates."""
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return filter_nodup_head(
                x, tail, filter(decide, tail), decide(x), unique,
                filter_nodup(decide, tail, unique.snd),
                lambda member: filter_mem(decide, x, tail, member).fst,
            )


@dependent(decreases="xs")
def count[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return add(decision_weight(decide(x)), count(decide, tail))


@theorem(decreases="d")
def length_filter_head[A: Type, P: Type](x: A, d: Decidable[P], tail: List[A]) -> Eq[
    Nat, length(filter_head(x, d, tail)), add(decision_weight(d), length(tail))
]:
    match d:
        case Yes(_):
            return refl(S(length(tail)))
        case No(_):
            return refl(length(tail))


@theorem(decreases="xs")
def length_filter_eq_count[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Eq[Nat, length(filter(decide, xs)), count(decide, xs)]:
    """The filtered list has exactly as many entries as the predicate count."""
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(
                length_filter_head(x, decide(x), filter(decide, tail)),
                cong(lambda n: add(decision_weight(decide(x)), n), length_filter_eq_count(decide, tail)),
            )


@theorem(decreases="d")
def count_head_le[P: Type](d: Decidable[P], counted: Nat, total: Nat, bound: LE[counted, total]) -> LE[
    add(decision_weight(d), counted), S(total)
]:
    match d:
        case Yes(_):
            return LESucc(counted, total, bound)
        case No(_):
            return le_step(bound)


@theorem(decreases="xs")
def count_le_length[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> LE[count(decide, xs), length(xs)]:
    """A predicate count cannot exceed the list length."""
    match xs:
        case Nil():
            return LEZero(0)
        case Cons(x, tail):
            return count_head_le(decide(x), count(decide, tail), length(tail), count_le_length(decide, tail))


@theorem
def length_filter_le[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> LE[length(filter(decide, xs)), length(xs)]:
    """Filtering does not increase length."""
    return transport[Nat, count(decide, xs), length(filter(decide, xs))](
        lambda n: LE[n, length(xs)], sym(length_filter_eq_count(decide, xs)), count_le_length(decide, xs)
    )


@dependent
def reject_head[A: Type, P: Type](x: A, d: Decidable[P], tail: List[A]) -> List[A]:
    match d:
        case Yes(_):
            return tail
        case No(_):
            return Cons(x, tail)


@dependent(decreases="xs")
def reject[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> List[A]:
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(x, tail):
            return reject_head(x, decide(x), reject(decide, tail))


@theorem(decreases="d")
def count_split_head[A: Type, P: Type](x: A, d: Decidable[P], rest: List[A], n: Nat) -> Eq[
    Nat, add(add(decision_weight(d), n), length(reject_head(x, d, rest))), S(add(n, length(rest)))
]:
    match d:
        case Yes(_):
            return refl(S(add(n, length(rest))))
        case No(_):
            return add_succ(n, length(rest))


@theorem(decreases="xs")
def count_split[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Eq[Nat, add(count(decide, xs), length(reject(decide, xs))), length(xs)]:
    """Selected count plus rejected length equals the original length."""
    match xs:
        case Nil():
            return refl(0)
        case Cons(x, tail):
            return trans(
                count_split_head(x, decide(x), reject(decide, tail), count(decide, tail)),
                cong(lambda n: S(n), count_split(decide, tail)),
            )


@inductive
class Removal[A: Type, x: A]:
    r"""Evidence that one occurrence of ``x`` was removed.

    ``source`` is the original list index and ``rest`` is the resulting list
    index. ``RemoveHere`` removes the head; ``RemoveThere.head`` preserves a
    preceding element while ``RemoveThere.step`` records the recursive removal.
    """
    source: Index[List[A]]
    rest: Index[List[A]]

    @constructor
    def RemoveHere(tail: List[A]) -> Removal[A, x, Cons(x, tail), tail]: ...
    @constructor
    def RemoveThere(head: A, ys: List[A], zs: List[A], step: Removal[A, x, ys, zs]) -> Removal[A, x, Cons(head, ys), Cons(head, zs)]: ...


@theorem(decreases="xs")
def find_removal[A: Type](x: A, xs: List[A], member: Mem(x, xs)) -> Sigma[List[A], lambda rest: Removal[A, x, xs, rest]]:
    r"""Theorem ``find_removal``: membership constructively yields a remainder and removal proof."""
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
                    return Pair(Cons(y, found.fst), RemoveThere[A, x](y, tail, found.fst, found.snd))


@theorem(decreases="r")
def removal_mem[A: Type, x: A, ys: List[A], zs: List[A]](r: Removal[A, x, ys, zs]) -> Mem(x, ys):
    match r:
        case RemoveHere(tail):
            return Left(refl(x))
        case RemoveThere(head, before, after, step):
            return Right(removal_mem(step))


@theorem(decreases="r")
def removal_length[A: Type, x: A, ys: List[A], zs: List[A]](r: Removal[A, x, ys, zs]) -> Eq[Nat, length(ys), S(length(zs))]:
    r"""Theorem ``removal_length``: removing one element decreases length by one."""
    match r:
        case RemoveHere(tail):
            return refl(S(length(tail)))
        case RemoveThere(head, before, after, step):
            return cong(lambda n: S(n), removal_length(step))


@theorem(decreases="xs")
def map_mem[A: Type, B: Type](f: Pi[A, lambda _: B], x: A, xs: List[A], member: Mem(x, xs)) -> Mem(f(x), map(f, xs)):
    match xs:
        case Nil():
            return absurd(Mem(f(x), Nil[B]()), member)
        case Cons(y, tail):
            return sum_elim[Eq[A, x, y], Mem(x, tail), Mem(f(x), Cons(f(y), map(f, tail)))](
                member,
                lambda eq: Left(cong(f, eq)),
                lambda later: Right(map_mem(f, x, tail, later)),
            )


@theorem(decreases="xs")
def map_mem_reflect[A: Type, B: Type](
    f: Pi[A, lambda _: B],
    injective: Pi[A, lambda x: Pi[A, lambda y: Pi[Eq[B, f(x), f(y)], lambda _: Eq[A, x, y]]]],
    x: A, xs: List[A], member: Mem(f(x), map(f, xs)),
) -> Mem(x, xs):
    """An injective map reflects membership."""
    match xs:
        case Nil():
            return absurd(Mem(x, Nil[A]()), member)
        case Cons(y, tail):
            return sum_elim[Eq[B, f(x), f(y)], Mem(f(x), map(f, tail)), Mem(x, Cons(y, tail))](
                member,
                lambda eq: Left(injective(x)(y)(eq)),
                lambda later: Right(map_mem_reflect(f, injective, x, tail, later)),
            )


@theorem(decreases="xs")
def map_nodup[A: Type, B: Type](
    f: Pi[A, lambda _: B],
    injective: Pi[A, lambda x: Pi[A, lambda y: Pi[Eq[B, f(x), f(y)], lambda _: Eq[A, x, y]]]],
    xs: List[A], unique: NoDup(xs),
) -> NoDup(map(f, xs)):
    """An injective map preserves duplicate-freeness."""
    match xs:
        case Nil():
            return MkUnit()
        case Cons(x, tail):
            return Pair(
                lambda member: unique.fst(map_mem_reflect(f, injective, x, tail, member)),
                map_nodup(f, injective, tail, unique.snd),
            )
