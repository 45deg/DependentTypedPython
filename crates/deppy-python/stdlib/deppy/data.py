from __future__ import annotations
from deppy._builtins import inductive, constructor, dependent, Type, Pi


@inductive
class Empty:
    pass


@inductive
class Unit:
    @constructor
    def MkUnit() -> Unit: ...


@inductive
class Bool:
    @constructor
    def False_() -> Bool: ...
    @constructor
    def True_() -> Bool: ...


@inductive
class Sum[A: Type, B: Type]:
    @constructor
    def Left(value: A) -> Sum[A, B]: ...
    @constructor
    def Right(value: B) -> Sum[A, B]: ...


@inductive
class Option[A: Type]:
    @constructor
    def None_() -> Option[A]: ...
    @constructor
    def Some(value: A) -> Option[A]: ...


@dependent
def Not(P: Type) -> Type:
    return Pi[P, lambda _: Empty]


@inductive
class Decidable[P: Type]:
    @constructor
    def Yes(proof: P) -> Decidable[P]: ...
    @constructor
    def No(refutation: Not(P)) -> Decidable[P]: ...
