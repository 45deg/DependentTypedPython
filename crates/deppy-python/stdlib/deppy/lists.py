from __future__ import annotations
from deppy._builtins import inductive, constructor, Index, dependent, theorem, Type, Pi, Sigma, Pair, Nat, Z, S, Eq, refl, absurd
from deppy.equality import cong, trans, transport
from deppy.data import Empty, Unit, MkUnit, Sum, Left, Right, Not, Decidable, Yes, No, sum_elim, decision_weight
from deppy.nat import add


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


@dependent(decreases="xs")
def append[A: Type](xs: List[A], ys: List[A]) -> List[A]:
    r"""Concatenate ``xs`` and ``ys``."""
    match xs:
        case Nil():
            return ys
        case Cons(h, t):
            return Cons(h, append(t, ys))


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


@dependent(decreases="xs")
def count[A: Type, P: Pi[A, lambda _: Type]](
    decide: Pi[A, lambda x: Decidable[P(x)]], xs: List[A]
) -> Nat:
    match xs:
        case Nil():
            return 0
        case Cons(x, tail):
            return add(decision_weight(decide(x)), count(decide, tail))


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
