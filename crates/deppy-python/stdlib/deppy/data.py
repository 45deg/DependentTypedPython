from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, Type, Pi, Sigma, Pair, Nat, Eq, refl, absurd
from deppy.equality import transport


@inductive
class Empty:
    r"""The uninhabited proposition :math:`\bot`."""
    pass


@inductive
class Unit:
    r"""The always-true proposition :math:`\top`, inhabited by ``MkUnit``."""
    @constructor
    def MkUnit() -> Unit: ...


@inductive
class Bool:
    r"""A two-valued boolean with constructors ``False_`` and ``True_``."""
    @constructor
    def False_() -> Bool: ...
    @constructor
    def True_() -> Bool: ...


@inductive
class Sum[A: Type, B: Type]:
    r"""Disjoint sum :math:`A + B`; ``Left`` and ``Right`` identify the chosen side."""
    @constructor
    def Left(value: A) -> Sum[A, B]: ...
    @constructor
    def Right(value: B) -> Sum[A, B]: ...


@inductive
class Option[A: Type]:
    r"""An optional ``A``, represented by ``None_`` or ``Some(value)``."""
    @constructor
    def None_() -> Option[A]: ...
    @constructor
    def Some(value: A) -> Option[A]: ...


@dependent
def Not(P: Type) -> Type:
    r"""Logical negation :math:`\neg P`, defined as :math:`P \to \bot`."""
    return Pi[P, lambda _: Empty]


@inductive
class Decidable[P: Type]:
    r"""A constructive decision for proposition ``P``.

    ``Yes.proof`` contains evidence of :math:`P`. ``No.refutation`` contains
    a function :math:`P \to \bot` proving :math:`\neg P`.
    """
    @constructor
    def Yes(proof: P) -> Decidable[P]: ...
    @constructor
    def No(refutation: Not(P)) -> Decidable[P]: ...


@dependent
def sum_elim[A: Type, B: Type, C: Type](
    value: Sum[A, B], left: Pi[A, lambda _: C], right: Pi[B, lambda _: C]
) -> C:
    r"""Eliminate a sum by supplying handlers for its left and right values."""
    match value:
        case Left(x):
            return left(x)
        case Right(y):
            return right(y)


@dependent
def decide_not[P: Type](d: Decidable[P]) -> Decidable[Not(P)]:
    r"""Decide :math:`\neg P` from a decision for :math:`P`."""
    match d:
        case Yes(p):
            return No[Not(P)](lambda np: np(p))
        case No(np):
            return Yes[Not(P)](np)


@dependent
def decide_and[P: Type, Q: Type](dp: Decidable[P], dq: Decidable[Q]) -> Decidable[Sigma[P, lambda _: Q]]:
    r"""Decide conjunction :math:`P \land Q`."""
    match dp:
        case Yes(p):
            match dq:
                case Yes(q):
                    return Yes[Sigma[P, lambda _: Q]](Pair(p, q))
                case No(nq):
                    return No[Sigma[P, lambda _: Q]](lambda both: nq(both.snd))
        case No(np):
            return No[Sigma[P, lambda _: Q]](lambda both: np(both.fst))


@dependent
def decide_or[P: Type, Q: Type](dp: Decidable[P], dq: Decidable[Q]) -> Decidable[Sum[P, Q]]:
    r"""Decide disjunction :math:`P \lor Q`."""
    match dp:
        case Yes(p):
            return Yes[Sum[P, Q]](Left[P, Q](p))
        case No(np):
            match dq:
                case Yes(q):
                    return Yes[Sum[P, Q]](Right[P, Q](q))
                case No(nq):
                    return No[Sum[P, Q]](lambda either: sum_elim[P, Q, Empty](either, np, nq))


@dependent
def decide_implies[P: Type, Q: Type](dp: Decidable[P], dq: Decidable[Q]) -> Decidable[Pi[P, lambda _: Q]]:
    r"""Decide implication :math:`P \to Q`."""
    match dp:
        case Yes(p):
            match dq:
                case Yes(q):
                    return Yes[Pi[P, lambda _: Q]](lambda _: q)
                case No(nq):
                    return No[Pi[P, lambda _: Q]](lambda implication: nq(implication(p)))
        case No(np):
            return Yes[Pi[P, lambda _: Q]](lambda p: absurd(Q, np(p)))


@dependent
def decision_weight[P: Type](d: Decidable[P]) -> Nat:
    r"""Return one for ``Yes`` and zero for ``No``."""
    match d:
        case Yes(_):
            return 1
        case No(_):
            return 0


@dependent(decreases="d")
def weight_yes[P: Type](d: Decidable[P], p: P) -> Eq[Nat, decision_weight(d), 1]:
    r"""Theorem ``weight_yes``: an inhabited proposition has decision weight one."""
    match d:
        case Yes(_):
            return refl(1)
        case No(np):
            return absurd(Eq[Nat, 0, 1], np(p))


@dependent(decreases="d")
def weight_no[P: Type](d: Decidable[P], np: Not(P)) -> Eq[Nat, decision_weight(d), 0]:
    r"""Theorem ``weight_no``: a refuted proposition has decision weight zero."""
    match d:
        case Yes(p):
            return absurd(Eq[Nat, 1, 0], np(p))
        case No(_):
            return refl(0)


@dependent
def weight_transport[A: Type, P: Pi[A, lambda _: Type], x: A, y: A](
    dec: Pi[A, lambda q: Decidable[P(q)]], eq: Eq[A, x, y]
) -> Eq[Nat, decision_weight(dec(x)), decision_weight(dec(y))]:
    r"""Decision weights are invariant under transport along :math:`x=y`."""
    return transport[A, x, y](lambda z: Eq[Nat, decision_weight(dec(x)), decision_weight(dec(z))], eq, refl(decision_weight(dec(x))))
