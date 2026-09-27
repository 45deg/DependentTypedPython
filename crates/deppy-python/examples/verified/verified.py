from deppy import Nat, S, Eq, refl
from deppy.nat import add
from deppy.data import Bool
from deppy.nat_order import LE, LT
from deppy.verified import verified, select_post


@verified(
    ensures=lambda n, result: Eq[Nat, result, add(n, n)],
    proof=lambda n, pre: refl(add(n, n)),
)
def twice(n: Nat) -> Nat:
    r"""Return :math:`2n` using a reassigned local."""
    x = n
    x = x + n
    return x


@verified(
    requires=lambda n, limit: LT(n, limit),
    ensures=lambda n, limit, result: LE[result, limit],
    proof=lambda n, limit, pre: pre,
)
def advance(n: Nat, limit: Nat) -> Nat:
    r"""Stay within the bound: :math:`n < l \Rightarrow n+1 \le l`."""
    n = S(n)
    return n


@verified(
    ensures=lambda flag, n, result: Eq[Nat, result, n],
    proof=lambda flag, n, pre: select_post[Nat, lambda result: Eq[Nat, result, n]](flag, n, n, refl(n), refl(n)),
)
def choose(flag: Bool, n: Nat) -> Nat:
    r"""Both branches return :math:`n`, with different sequences of assignments."""
    if flag:
        x = 0
        x = n
    else:
        x = n
    return x
