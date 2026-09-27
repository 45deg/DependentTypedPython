from __future__ import annotations
from deppy import inductive, constructor, dependent, Nat, nat_elim, S, Eq, refl


@dependent
def plus(n: Nat, m: Nat) -> Nat:
    return nat_elim(0, lambda _: Nat, m, lambda k, ih: S(ih), n)


@inductive
class Tree:
    @constructor
    def Leaf() -> Tree: ...
    @constructor
    def Node(left: Tree, right: Tree) -> Tree: ...


@dependent(decreases='tree')
def size(tree: Tree) -> Nat:
    match tree:
        case Leaf():
            return 1
        case Node(left, right):
            return plus(size(left), size(right))


@dependent
def proof() -> Eq[Nat, size(Node(Leaf(), Node(Leaf(), Leaf()))), 3]:
    return refl(3)
