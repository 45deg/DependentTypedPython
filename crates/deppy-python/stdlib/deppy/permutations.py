from deppy._builtins import inductive, constructor, Index, theorem, Type, Pi, Nat, S, Eq, refl, absurd, Pair
from deppy.equality import sym, trans, cong
from deppy.data import Empty, Sum, Left, Right, sum_elim, MkUnit
from deppy.lists import List, Nil, Cons, Mem, NoDup, length, map


@inductive
class Permutation[A: Type]:
    """Evidence that two lists differ only by a finite sequence of adjacent swaps."""
    source: Index[List[A]]
    target: Index[List[A]]

    @constructor
    def PermNil() -> Permutation[A, Nil[A](), Nil[A]()]: ...

    @constructor
    def PermCons(x: A, xs: List[A], ys: List[A], tail: Permutation[A, xs, ys]) -> Permutation[
        A, Cons(x, xs), Cons(x, ys)
    ]: ...

    @constructor
    def PermSwap(x: A, y: A, xs: List[A]) -> Permutation[
        A, Cons(x, Cons(y, xs)), Cons(y, Cons(x, xs))
    ]: ...

    @constructor
    def PermTrans(xs: List[A], ys: List[A], zs: List[A], first: Permutation[A, xs, ys],
                  second: Permutation[A, ys, zs]) -> Permutation[A, xs, zs]: ...


@theorem(decreases="xs")
def perm_refl[A: Type](xs: List[A]) -> Permutation[A, xs, xs]:
    """Every list is a permutation of itself."""
    match xs:
        case Nil():
            return PermNil[A]()
        case Cons(x, tail):
            return PermCons(x, tail, tail, perm_refl(tail))


@theorem(decreases="p")
def perm_sym[A: Type, xs: List[A], ys: List[A]](p: Permutation[A, xs, ys]) -> Permutation[A, ys, xs]:
    """Reverse a permutation proof."""
    match p:
        case PermNil():
            return PermNil[A]()
        case PermCons(x, before, after, tail):
            return PermCons(x, after, before, perm_sym(tail))
        case PermSwap(x, y, rest):
            return PermSwap(y, x, rest)
        case PermTrans(first, middle, last, left, right):
            return PermTrans(last, middle, first, perm_sym(right), perm_sym(left))


@theorem
def perm_trans[A: Type, xs: List[A], ys: List[A], zs: List[A]](
    first: Permutation[A, xs, ys], second: Permutation[A, ys, zs]
) -> Permutation[A, xs, zs]:
    """Compose two permutation proofs."""
    return PermTrans(xs, ys, zs, first, second)


@theorem(decreases="p")
def perm_length[A: Type, xs: List[A], ys: List[A]](p: Permutation[A, xs, ys]) -> Eq[
    Nat, length(xs), length(ys)
]:
    """Permutation preserves list length."""
    match p:
        case PermNil():
            return refl(0)
        case PermCons(x, before, after, tail):
            return cong(lambda n: S(n), perm_length(tail))
        case PermSwap(x, y, rest):
            return refl(S(S(length(rest))))
        case PermTrans(first, middle, last, left, right):
            return trans(perm_length(left), perm_length(right))


@theorem
def swap_mem[A: Type](q: A, x: A, y: A, xs: List[A], member: Mem(q, Cons(x, Cons(y, xs)))) -> Mem(
    q, Cons(y, Cons(x, xs))
):
    return sum_elim[Eq[A, q, x], Mem(q, Cons(y, xs)), Mem(q, Cons(y, Cons(x, xs)))](
        member,
        lambda equal: Right(Left(equal)),
        lambda later: sum_elim[Eq[A, q, y], Mem(q, xs), Mem(q, Cons(y, Cons(x, xs)))](
            later, lambda equal: Left(equal), lambda tail: Right(Right(tail))
        ),
    )


@theorem(decreases="p")
def perm_mem[A: Type, xs: List[A], ys: List[A]](
    p: Permutation[A, xs, ys], q: A, member: Mem(q, xs)
) -> Mem(q, ys):
    """A permutation preserves membership."""
    match p:
        case PermNil():
            return absurd(Mem(q, Nil[A]()), member)
        case PermCons(x, before, after, tail):
            return sum_elim[Eq[A, q, x], Mem(q, before), Mem(q, Cons(x, after))](
                member, lambda equal: Left(equal), lambda later: Right(perm_mem(tail, q, later))
            )
        case PermSwap(x, y, rest):
            return swap_mem(q, x, y, rest, member)
        case PermTrans(first, middle, last, left, right):
            middle_member = perm_mem(left, q, member)
            return perm_mem(right, q, middle_member)


@theorem
def perm_mem_back[A: Type, xs: List[A], ys: List[A]](
    p: Permutation[A, xs, ys], q: A, member: Mem(q, ys)
) -> Mem(q, xs):
    """Transport membership backward through a permutation."""
    return perm_mem(perm_sym(p), q, member)


@theorem
def swap_nodup[A: Type](x: A, y: A, xs: List[A], unique: NoDup(Cons(x, Cons(y, xs)))) -> NoDup(
    Cons(y, Cons(x, xs))
):
    return Pair(
        lambda member: sum_elim[Eq[A, y, x], Mem(y, xs), Empty](
            member,
            lambda equal: unique.fst(Left(sym(equal))),
            lambda later: unique.snd.fst(later),
        ),
        Pair(lambda member: unique.fst(Right(member)), unique.snd.snd),
    )


@theorem(decreases="p")
def perm_nodup[A: Type, xs: List[A], ys: List[A]](
    p: Permutation[A, xs, ys], unique: NoDup(xs)
) -> NoDup(ys):
    """A permutation preserves duplicate-freeness."""
    match p:
        case PermNil():
            return MkUnit()
        case PermCons(x, before, after, tail):
            return Pair(
                lambda member: unique.fst(perm_mem_back(tail, x, member)),
                perm_nodup(tail, unique.snd),
            )
        case PermSwap(x, y, rest):
            return swap_nodup(x, y, rest, unique)
        case PermTrans(first, middle, last, left, right):
            middle_unique = perm_nodup(left, unique)
            return perm_nodup(right, middle_unique)


@theorem(decreases="p")
def perm_map[A: Type, B: Type, xs: List[A], ys: List[A]](
    f: Pi[A, lambda _: B], p: Permutation[A, xs, ys]
) -> Permutation[B, map(f, xs), map(f, ys)]:
    """Mapping preserves an explicit permutation."""
    match p:
        case PermNil():
            return PermNil[B]()
        case PermCons(x, before, after, tail):
            return PermCons(f(x), map(f, before), map(f, after), perm_map(f, tail))
        case PermSwap(x, y, rest):
            return PermSwap(f(x), f(y), map(f, rest))
        case PermTrans(first, middle, last, left, right):
            return PermTrans(map(f, first), map(f, middle), map(f, last), perm_map(f, left), perm_map(f, right))
