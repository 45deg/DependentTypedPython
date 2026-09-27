from __future__ import annotations
from deppy import Nat
from deppy.verified import verified
from deppy.verified_loop import decreases
from deppy.integer import Int, of_nat, neg


@verified
def subtract(a: Nat, b: Nat) -> Nat:
    if b <= a:
        return a - b
    return 0


@verified
def gcd(a: Nat, b: Nat) -> Nat:
    x = a
    y = b
    while 0 < y:
        decreases(y)
        x, y = y, x % y
    return x


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
