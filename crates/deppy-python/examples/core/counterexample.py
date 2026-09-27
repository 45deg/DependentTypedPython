from __future__ import annotations
from deppy import dependent, Nat, Eq, refl


@dependent
def false_by_definitional_equality(n: Nat) -> Eq[Nat, n + 0, n]:
    # `n + 0` is not definitionally equal to `n`: addition recurses on
    # its first argument, so this cannot be proved by reflexivity.
    return refl(n)
