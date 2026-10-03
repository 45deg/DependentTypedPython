from deppy import dependent, Nat, Eq
from deppy.data import Empty
from deppy.nat_order import LE, LT, le_antisymm, lt_irrefl, lt_trans


# Part 5: order propositions are types whose values are proofs.
# LE[n, m] means n ≤ m; LT(n, m) means n < m; Empty has no values.


@dependent
def same_if_both_ways(n: Nat, m: Nat, forward: LE[n, m], backward: LE[m, n]) -> Eq[Nat, n, m]:
    # Antisymmetry: n ≤ m ∧ m ≤ n → n = m.
    # Both inequalities are proof arguments; no numeric search is needed here.
    return le_antisymm(forward, backward)


@dependent
def no_strict_cycle(n: Nat, m: Nat, forward: LT(n, m), backward: LT(m, n)) -> Empty:
    # n < m ∧ m < n → n < n, contradicting irreflexivity.
    # Returning Empty proves these two assumptions cannot hold together.
    return lt_irrefl(n, lt_trans(n, m, n, forward, backward))


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    # Equality proofs print as <erased proof>: Python does not check their claims.
    from deppy.nat_order import le_decide, lt_decide, le_refl
    from deppy.data import Yes

    for n, m in ((2, 5), (5, 2), (3, 3)):
        print(f"{n} <= {m}: {isinstance(le_decide(n, m), Yes)}")
        print(f"{n} < {m}: {isinstance(lt_decide(n, m), Yes)}")
    print(f"3 <= 3 in both directions: {same_if_both_ways(3, 3, le_refl(3), le_refl(3))}")
