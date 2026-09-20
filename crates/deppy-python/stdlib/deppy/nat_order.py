from __future__ import annotations
from deppy._builtins import inductive, constructor, Index, dependent, Nat, Z, S, Type, Eq, refl, absurd
from deppy.data import Empty, Unit, MkUnit, Decidable, Yes, No


@inductive
class LE:
    left: Index[Nat]
    right: Index[Nat]

    @constructor
    def LEZero(n: Nat) -> LE[0, n]: ...
    @constructor
    def LESucc(n: Nat, m: Nat, step: LE[n, m]) -> LE[S(n), S(m)]: ...


@dependent
def LT(n: Nat, m: Nat) -> Type:
    return LE[S(n), m]


@dependent(decreases="n")
def le_refl(n: Nat) -> LE[n, n]:
    match n:
        case Z():
            return LEZero(0)
        case S(k):
            return LESucc(k, k, le_refl(k))


@dependent(decreases="p")
def le_step[n: Nat, m: Nat](p: LE[n, m]) -> LE[n, S(m)]:
    match p:
        case LEZero(k):
            return LEZero(S(k))
        case LESucc(a, b, q):
            return LESucc(a, S(b), le_step(q))


@dependent(decreases="p")
def le_pred(n: Nat, m: Nat, p: LE[S(n), S(m)]) -> LE[n, m]:
    match p:
        case LESucc(a, b, q):
            return q


@dependent(decreases="p")
def le_trans[n: Nat, m: Nat](p: LE[n, m], k: Nat, q: LE[m, k]) -> LE[n, k]:
    match p:
        case LEZero(_):
            return LEZero(k)
        case LESucc(a, b, step):
            match q:
                case LESucc(j, end, proof):
                    return LESucc(a, end, le_trans(step, end, proof))
