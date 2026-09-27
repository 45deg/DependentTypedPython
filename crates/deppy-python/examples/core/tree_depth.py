from deppy import inductive, constructor, dependent, Pi, Nat, S, induct, Eq, refl


@inductive
class Tree:
    @constructor
    def Leaf() -> Tree: ...
    @constructor
    def Node(children: Pi[Nat, lambda _: Tree]) -> Tree: ...


@dependent
def depth(tree: Tree) -> Nat:
    return induct(0, tree, lambda _: Nat, 0, lambda children, ih: S(ih(0)))


@dependent
def proof() -> Eq[Nat, depth(Node(lambda n: Leaf())), 1]:
    return refl(1)
