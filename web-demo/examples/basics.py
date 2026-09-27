from deppy import dependent, Type, Nat, Z, S, Eq, refl, Sigma, Pair, Vec, VNil


# Basics: @dependent functions are checked statically; their bodies are not
# executed as ordinary Python to establish a proof.
# Nat has constructors Z() = 0 and S(n) = n + 1.


@dependent
def identity[A: Type](x: A) -> A:
    # The same implementation works for any type A: x ↦ x.
    return x


@dependent
def twice(n: Nat) -> Nat:
    # Local names can carry explicit types or have their types inferred.
    first: Nat = S(n)
    second = S(first)
    return identity(second)


@dependent
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    # Eq[Nat, n, n] states n = n; refl(n) is its proof.
    proof = refl(n)
    return proof


@dependent
def empty(n: Nat) -> Vec[Nat, Z()]:
    # VNil() is a vector with length 0, regardless of n.
    return VNil()


@dependent
def pack[T: Type](n: Nat, xs: Vec[T, n]) -> Sigma[Nat, lambda k: Vec[T, k]]:
    # A dependent pair stores k together with a vector of length k.
    return Pair(n, xs)


@dependent
def identity_zero() -> Eq[Nat, identity(Z()), Z()]:
    # A checked equality, rather than a Python assert: identity(0) = 0.
    return refl(Z())
