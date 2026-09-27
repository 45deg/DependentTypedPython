from deppy import dependent, Nat, Eq
from deppy.lists import List, Nil, Cons, append, map, reverse, append_assoc, map_identity, reverse_involution


# Part 4: reuse checked library lemmas for concrete list expressions.
# Nil[Nat]() is [], and Cons(x, xs) is x :: xs.


@dependent
def append_brackets() -> Eq[List[Nat], append(append(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]())), Nil[Nat]()), append(Cons(0, Nil[Nat]()), append(Cons(1, Nil[Nat]()), Nil[Nat]()))]:
    # Associativity: (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
    # Instantiate the library theorem with xs = [0], ys = [1], zs = [].
    return append_assoc(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]()), Nil[Nat]())


@dependent
def map_same() -> Eq[List[Nat], map(lambda x: x, Cons(0, Nil[Nat]())), Cons(0, Nil[Nat]())]:
    # Identity map: map(id, xs) = xs.
    # The argument here is the one-element list [0].
    return map_identity(Cons(0, Nil[Nat]()))


@dependent
def reverse_twice() -> Eq[List[Nat], reverse(reverse(Cons(0, Cons(1, Nil[Nat]())))), Cons(0, Cons(1, Nil[Nat]()))]:
    # Involution: reverse(reverse(xs)) = xs.
    # The library proof applies to the concrete list [0, 1].
    return reverse_involution(Cons(0, Cons(1, Nil[Nat]())))
