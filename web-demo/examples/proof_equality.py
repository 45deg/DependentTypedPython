from deppy import dependent, Nat, Eq, refl, sym, trans, cong, S


# Part 1: equality proofs. Eq[Nat, a, b] means a = b for natural numbers.
# Each function returns a proof term; the checker verifies its stated type.


@dependent
def same(n: Nat) -> Eq[Nat, n, n]:
    # Reflexivity: ∀n, n = n.
    return refl(n)


@dependent
def turn_around(n: Nat, m: Nat, proof: Eq[Nat, n, m]) -> Eq[Nat, m, n]:
    # Symmetry: n = m → m = n.
    return sym(proof)


@dependent
def chain(n: Nat, m: Nat, k: Nat, first: Eq[Nat, n, m], second: Eq[Nat, m, k]) -> Eq[Nat, n, k]:
    # Transitivity: n = m ∧ m = k → n = k.
    return trans(first, second)


@dependent
def successor_preserves(n: Nat, m: Nat, proof: Eq[Nat, n, m]) -> Eq[Nat, S(n), S(m)]:
    # Congruence: n = m → S(n) = S(m).
    return cong(S, proof)
