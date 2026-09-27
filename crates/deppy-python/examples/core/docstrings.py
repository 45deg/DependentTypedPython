from deppy import inductive, constructor, dependent, Nat, Z, S, Eq, refl


@inductive
class Flag:
    """A documented proposition."""
    @constructor
    def On() -> Flag:
        """The sole constructor."""
        ...


@dependent
def identity(n: Nat) -> Nat:
    """Return :math:`n`."""
    return n


@dependent(decreases="n")
def proof(n: Nat) -> Eq[Nat, identity(n), n]:
    """Identity theorem."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return refl(S(k))
