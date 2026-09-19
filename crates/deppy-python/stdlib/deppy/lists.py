from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, Type, Pi, Eq, refl
from deppy.equality import cong, trans


@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...


@dependent(decreases="xs")
def append[A: Type](xs: List[A], ys: List[A]) -> List[A]:
    match xs:
        case Nil():
            return ys
        case Cons(h, t):
            return Cons(h, append(t, ys))


@dependent(decreases="xs")
def map[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> List[B]:
    match xs:
        case Nil():
            return Nil[B]()
        case Cons(h, t):
            return Cons(f(h), map(f, t))


@dependent(decreases="xs")
def append_assoc[A: Type](xs: List[A], ys: List[A], zs: List[A]) -> Eq[List[A], append(append(xs, ys), zs), append(xs, append(ys, zs))]:
    match xs:
        case Nil():
            return refl(append(ys, zs))
        case Cons(h, t):
            return cong(lambda rest: Cons(h, rest), append_assoc(t, ys, zs))


@dependent(decreases="xs")
def map_identity[A: Type](xs: List[A]) -> Eq[List[A], map(lambda x: x, xs), xs]:
    match xs:
        case Nil():
            return refl(Nil[A]())
        case Cons(h, t):
            return cong(lambda rest: Cons(h, rest), map_identity(t))


@dependent(decreases="xs")
def map_composition[A: Type, B: Type, C: Type](f: Pi[A, lambda _: B], g: Pi[B, lambda _: C], xs: List[A]) -> Eq[List[C], map(g, map(f, xs)), map(lambda x: g(f(x)), xs)]:
    match xs:
        case Nil():
            return refl(Nil[C]())
        case Cons(h, t):
            return cong(lambda rest: Cons(g(f(h)), rest), map_composition(f, g, t))


@dependent(decreases="xs")
def snoc[A: Type](xs: List[A], x: A) -> List[A]:
    match xs:
        case Nil():
            return Cons(x, Nil[A]())
        case Cons(h, t):
            return Cons(h, snoc(t, x))


@dependent(decreases="xs")
def reverse[A: Type](xs: List[A]) -> List[A]:
    match xs:
        case Nil():
            return Nil[A]()
        case Cons(h, t):
            return snoc(reverse(t), h)


@dependent(decreases="xs")
def reverse_snoc[A: Type](xs: List[A], x: A) -> Eq[List[A], reverse(snoc(xs, x)), Cons(x, reverse(xs))]:
    match xs:
        case Nil():
            return refl(Cons(x, Nil[A]()))
        case Cons(h, t):
            return cong[List[A], List[A]](lambda rest: snoc(rest, h), reverse_snoc(t, x))


@dependent(decreases="xs")
def reverse_involution[A: Type](xs: List[A]) -> Eq[List[A], reverse(reverse(xs)), xs]:
    match xs:
        case Nil():
            return refl(Nil[A]())
        case Cons(h, t):
            return trans(reverse_snoc(reverse(t), h), cong(lambda rest: Cons(h, rest), reverse_involution(t)))
