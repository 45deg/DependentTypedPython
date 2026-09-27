from __future__ import annotations
from deppy import dependent, Nat, Z, S, Eq, refl, cong


# Part 2: prove a property for every natural number by structural induction.
# Here 0 is Z(), S(k) is k + 1, and n + 0 does not reduce for unknown n.


@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, n + 0, n]:
    # Goal: ∀n : Nat, n + 0 = n.
    match n:
        case Z():
            # Base case: 0 + 0 = 0, so reflexivity closes the goal.
            return refl(Z())
        case S(k):
            # Induction hypothesis: k + 0 = k.
            # Applying S to both sides gives S(k + 0) = S(k).
            return cong(S, zero_right(k))
