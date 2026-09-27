from deppy._builtins import inductive, constructor, Index, induct, absurd, dependent, Type, Pi, Nat, Z, S


@inductive
class IVec[A: Type]:
    """Demonstration vector indexed by the canonical Nat."""
    length: Index[Nat]
    @constructor
    def INil() -> IVec[A, Z()]: ...
    @constructor
    def ICons(k: Nat, head: A, tail: IVec[A, k]) -> IVec[A, S(k)]: ...


@inductive
class IFin:
    """Demonstration finite index bounded by the canonical Nat."""
    bound: Index[Nat]
    @constructor
    def IFZ(k: Nat) -> IFin[S(k)]: ...
    @constructor
    def IFS(k: Nat, pred: IFin[k]) -> IFin[S(k)]: ...


@dependent
def case_motive(size: Nat) -> Pi[IFin[size], lambda index: Type[1]]:
    return induct(
        2, size,
        lambda size: Pi[IFin[size], lambda index: Type[1]],
        lambda index: Type,
        lambda k, unused: lambda index: Pi[
            Pi[IFin[S(k)], lambda j: Type],
            lambda P: Pi[P(IFZ(k)), lambda first: Pi[
                Pi[IFin[k], lambda j: P(IFS(k, j))],
                lambda rest: P(index),
            ]],
        ],
    )


@dependent
def fin_case(k: Nat, P: Pi[IFin[S(k)], lambda index: Type], i: IFin[S(k)],
             first: P(IFZ(k)), rest: Pi[IFin[k], lambda j: P(IFS(k, j))]) -> P(i):
    return induct(
        1, i,
        lambda size, index: case_motive(size)(index),
        lambda k, family, zero, step: zero,
        lambda k, j, unused, family, zero, step: step(j),
    )(P)(first)(rest)


@dependent
def get[A: Type, n: Nat](xs: IVec[A, n], i: IFin[n]) -> A:
    """Look up an element using a demonstration finite index."""
    match xs:
        case INil():
            return absurd(A, i)
        case ICons(k, head, tail):
            match i:
                case IFZ(j):
                    return head
                case IFS(j, pred):
                    return get(tail, pred)
