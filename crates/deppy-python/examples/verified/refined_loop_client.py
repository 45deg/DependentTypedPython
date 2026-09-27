from deppy import theorem, Nat, Eq
from deppy.data import MkUnit
from deppy.verified import verified_spec
from refined_loop import bounded_countdown


@theorem
def countdown_correct(n: Nat) -> Eq[Nat, bounded_countdown(n), 0]:
    r"""Reuse the imported specification :math:`bounded\_countdown(n)=0`."""
    return verified_spec(bounded_countdown, n, MkUnit())
