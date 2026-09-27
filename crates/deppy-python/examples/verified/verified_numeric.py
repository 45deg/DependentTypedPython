from deppy import Nat, theorem
from deppy.data import MkUnit
from deppy.verified import verified, Refined, verified_spec
from deppy.verified_loop import invariant, decreases
from deppy.integer import Int, of_nat, neg
from gcd_proof import IsGCD, CommonEquiv, common_equiv_initial, common_equiv_step, gcd_exit


@verified
def subtract(a: Nat, b: Nat) -> Nat:
    if b <= a:
        return a - b
    return 0


@verified(proofs={
    "loop.init": lambda a, b, pre: common_equiv_initial(a, b),
    "loop.preserve": lambda a, b, pre, state, inv, test, value: common_equiv_step(a, b, state.fst, state.snd.fst, inv),
    "loop.exit": lambda a, b, pre, state, inv, test: gcd_exit(a, b, state.fst, state.snd.fst, inv, test),
})
def gcd(a: Nat, b: Nat) -> Refined[Nat, lambda result: IsGCD(a, b, result)]:
    x = a
    y = b
    while 0 < y:
        invariant(lambda x, y: CommonEquiv(a, b, x, y), state=(x, y))
        decreases(y)
        x, y = y, x % y
    return x


@theorem
def gcd_correct(a: Nat, b: Nat) -> IsGCD(a, b, gcd(a, b)):
    return verified_spec(gcd, a, b, MkUnit())


@verified
def lift(n: Nat) -> Int:
    return of_nat(n)


@verified
def negate(n: Int) -> Int:
    return -n


@verified
def signed_div(a: Int, b: Int) -> Int:
    if b != 0:
        return a // b
    return 0


@verified
def signed_mod(a: Int, b: Int) -> Int:
    if b != 0:
        return a % b
    return 0
