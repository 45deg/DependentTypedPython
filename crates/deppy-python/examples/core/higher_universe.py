from __future__ import annotations
from deppy import inductive, constructor, dependent, Type, Nat
@inductive(level=1)
class Box:
    @constructor
    def Pack(T: Type) -> Box: ...
@dependent
def value() -> Box:
    return Pack(Nat)
