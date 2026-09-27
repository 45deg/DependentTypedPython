from __future__ import annotations
from deppy import dependent, Nat, S, Eq
from deppy.lists import List, Nil, Cons, append, map, reverse, append_assoc, map_identity, map_composition, reverse_involution


@dependent
def assoc() -> Eq[List[Nat], append(append(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]())), Nil[Nat]()), append(Cons(0, Nil[Nat]()), append(Cons(1, Nil[Nat]()), Nil[Nat]()))]:
    return append_assoc(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]()), Nil[Nat]())


@dependent
def identity() -> Eq[List[Nat], map(lambda x: x, Cons(0, Nil[Nat]())), Cons(0, Nil[Nat]())]:
    return map_identity(Cons(0, Nil[Nat]()))


@dependent
def composition() -> Eq[List[Nat], map(lambda x: S(x), map(lambda x: S(x), Cons(0, Nil[Nat]()))), Cons(2, Nil[Nat]())]:
    return map_composition(lambda x: S(x), lambda x: S(x), Cons(0, Nil[Nat]()))


@dependent
def involution() -> Eq[List[Nat], reverse(reverse(Cons(0, Cons(1, Nil[Nat]())))), Cons(0, Cons(1, Nil[Nat]()))]:
    return reverse_involution(Cons(0, Cons(1, Nil[Nat]())))
