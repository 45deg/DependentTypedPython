from deppy import Nat, Eq, refl
from deppy.nat import add
from deppy.verified import verified


@verified(
    ensures=lambda n, result: Eq[Nat, result, add(n, n)],
    proof=lambda n, pre: refl(add(n, n)),
)
def twice(n: Nat) -> Nat:
    return n + n


if __name__ == "__main__":
    print(twice(21))
