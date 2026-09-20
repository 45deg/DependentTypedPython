from __future__ import annotations
from deppy._builtins import inductive, constructor, Index, dependent, Nat, Z, S, Type, Eq, refl, absurd
from deppy.data import Empty, Unit, MkUnit, Decidable, Yes, No


@inductive
class LE:
    r"""Evidence for :math:`n \le m`.

    ``left`` and ``right`` are the lower and upper natural-number indices.
    ``LEZero(m)`` proves :math:`0 \le m`; ``LESucc`` lifts a proof through
    successor on both sides.
    """
    left: Index[Nat]
    right: Index[Nat]

    @constructor
    def LEZero(n: Nat) -> LE[0, n]: ...
    @constructor
    def LESucc(n: Nat, m: Nat, step: LE[n, m]) -> LE[S(n), S(m)]: ...


@dependent
def LT(n: Nat, m: Nat) -> Type:
    r"""Strict order, defined by :math:`n < m \;\equiv\; n+1 \le m`."""
    return LE[S(n), m]


@dependent(decreases="n")
def le_refl(n: Nat) -> LE[n, n]:
    r"""Theorem ``le_refl``: :math:`n \le n`."""
    match n:
        case Z():
            return LEZero(0)
        case S(k):
            return LESucc(k, k, le_refl(k))


@dependent(decreases="p")
def le_step[n: Nat, m: Nat](p: LE[n, m]) -> LE[n, S(m)]:
    r"""Theorem ``le_step``: :math:`n \le m \Rightarrow n \le m+1`."""
    match p:
        case LEZero(k):
            return LEZero(S(k))
        case LESucc(a, b, q):
            return LESucc(a, S(b), le_step(q))


@dependent(decreases="p")
def le_pred(n: Nat, m: Nat, p: LE[S(n), S(m)]) -> LE[n, m]:
    r"""Cancel successor from both sides of an order proof."""
    match p:
        case LESucc(a, b, q):
            return q


@dependent(decreases="p")
def le_trans[n: Nat, m: Nat](p: LE[n, m], k: Nat, q: LE[m, k]) -> LE[n, k]:
    r"""Theorem ``le_trans``: :math:`n \le m \land m \le k \Rightarrow n \le k`."""
    match p:
        case LEZero(_):
            return LEZero(k)
        case LESucc(a, b, step):
            match q:
                case LESucc(j, end, proof):
                    return LESucc(a, end, le_trans(step, end, proof))
