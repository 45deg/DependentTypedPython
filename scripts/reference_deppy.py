"""Test-only execution model for the committed Python fixtures.

This is an independent reference for differential tests, not a trusted runtime,
proof checker, or an implementation of Checked/Dependent boundaries.
"""
from dataclasses import dataclass


class Nat:
    def __add__(self, other):
        return natural(integer(self) + (other if type(other) is int else integer(other)))


@dataclass(frozen=True)
class Z(Nat):
    pass


@dataclass(frozen=True)
class S(Nat):
    predecessor: Nat


def integer(n):
    result = 0
    while isinstance(n, S):
        result += 1
        n = n.predecessor
    assert isinstance(n, Z)
    return result


def natural(n):
    result = Z()
    for _ in range(n):
        result = S(result)
    return result


@dataclass(frozen=True)
class VNil:
    pass


@dataclass(frozen=True)
class VCons:
    length: Nat
    head: object
    tail: object


def vector(values):
    result = VNil()
    for i in range(len(values) - 1, -1, -1):
        result = VCons(natural(len(values) - i - 1), values[i], result)
    return result


@dataclass(frozen=True)
class FZ:
    bound: Nat


@dataclass(frozen=True)
class FS:
    bound: Nat
    predecessor: object


def index(bound, rank):
    result = FZ(natural(bound - rank - 1))
    for offset in range(rank):
        result = FS(natural(bound - rank + offset), result)
    return result


@dataclass(frozen=True)
class Pair:
    fst: object
    snd: object


@dataclass(frozen=True)
class Proof:
    value: object


def refl(value):
    return Proof(value)


def cong(function, proof):
    return Proof(function(proof.value))


def fin0_elim(value):
    raise AssertionError('reference reached an impossible Fin[0] branch')


def dependent(function=None, **options):
    return function if function is not None else lambda f: f


def record(cls=None, **options):
    return dataclass(cls, frozen=True) if cls is not None else lambda c: dataclass(c, frozen=True)


# Annotations are postponed in every fixture. These names are markers only.
Type = Vec = Fin = Eq = Sigma = Pi = object


def canonical(value):
    if isinstance(value, Nat):
        return integer(value)
    if isinstance(value, VNil):
        return ()
    if isinstance(value, VCons):
        return (canonical(value.head),) + canonical(value.tail)
    if isinstance(value, Pair):
        return (canonical(value.fst), canonical(value.snd))
    if isinstance(value, Proof):
        return None
    return value
