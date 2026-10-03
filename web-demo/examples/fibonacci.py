from deppy import dependent, theorem, Nat, Z, S, Type, Sigma, Eq, refl, Pair, absurd
from deppy.data import Bool, False_, True_, MkUnit
from deppy.equality import cong2, trans, sym
from deppy.tactics import rewrite, rewrite_in
from deppy.nat import add, add_zero, add_succ, pred_or
from deppy.verified import verified, Refined, verified_spec, nat_lt, false_ne_true
from deppy.verified_loop import invariant, decreases


# Verified Programs: compare a recursive Fibonacci specification with a loop.
# Goal: ∀n : Nat, fib_loop(n) = fib_recursive(n).
# F₀ = 0, F₁ = 1, and Fₙ₊₂ = Fₙ + Fₙ₊₁.


@dependent(decreases="n")
def fib_pair(n: Nat) -> Sigma[Nat, lambda _: Nat]:
    # Structural recursion returns the pair (Fₙ, Fₙ₊₁).
    match n:
        case Z():
            # Base case: (F₀, F₁) = (0, 1).
            return Pair(0, 1)
        case S(k):
            # Step: (Fₖ, Fₖ₊₁) ↦ (Fₖ₊₁, Fₖ + Fₖ₊₁).
            previous = fib_pair(k)
            return Pair(previous.snd, add(previous.fst, previous.snd))


@dependent
def fib_recursive(n: Nat) -> Nat:
    # The first component of the pair defines Fₙ.
    return fib_pair(n).fst


@theorem
def fib_step(n: Nat) -> Eq[Nat, add(fib_recursive(n), fib_recursive(S(n))), fib_recursive(S(S(n)))]:
    # Recurrence: Fₙ + Fₙ₊₁ = Fₙ₊₂ by reducing fib_pair.
    return refl(add(fib_recursive(n), fib_recursive(S(n))))


@dependent
def FibInvariant(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat) -> Type:
    # Invariant: remaining + index = n ∧ a = Fᵢ ∧ b = Fᵢ₊₁.
    # The nested Sigma stores a proof for each of these three claims.
    return Sigma[Eq[Nat, add(remaining, index), n], lambda count:
        Sigma[Eq[Nat, a, fib_recursive(index)], lambda current:
        Eq[Nat, b, fib_recursive(S(index))]]]


@theorem(decreases="remaining")
def counter_step(n: Nat, remaining: Nat, index: Nat, count: Eq[Nat, add(remaining, index), n], test: Eq[Bool, nat_lt(0, remaining), True_()]) -> Eq[Nat, add(pred_or(0, remaining), S(index)), n]:
    # If remaining > 0, then (remaining − 1) + (index + 1) = n.
    match remaining:
        case Z():
            # remaining = 0 contradicts the true loop guard.
            return absurd(Eq[Nat, add(pred_or(0, 0), S(index)), n], false_ne_true(test))
        case S(k):
            return trans(add_succ(k, index), count)


@theorem
def fib_preserve(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat, inv: FibInvariant(n, remaining, index, a, b), test: Eq[Bool, nat_lt(0, remaining), True_()]) -> FibInvariant(n, pred_or(0, remaining), S(index), b, add(a, b)):
    # Update (a, b) ↦ (b, a + b); the recurrence proves the new b = Fᵢ₊₂.
    # counter_step handles the remaining + index = n clause.
    return Pair(counter_step(n, remaining, index, inv.fst, test),
        Pair(inv.snd.snd,
            rewrite(inv.snd.fst, rewrite(inv.snd.snd, fib_step(index)))))


@theorem(decreases="remaining")
def counter_zero(remaining: Nat, test: Eq[Bool, nat_lt(0, remaining), False_()]) -> Eq[Nat, remaining, 0]:
    # ¬(0 < remaining) → remaining = 0 for natural numbers.
    match remaining:
        case Z():
            return refl(0)
        case S(k):
            return absurd(Eq[Nat, S(k), 0], false_ne_true(sym(test)))


@theorem
def fib_exit(n: Nat, remaining: Nat, index: Nat, a: Nat, b: Nat, inv: FibInvariant(n, remaining, index, a, b), test: Eq[Bool, nat_lt(0, remaining), False_()]) -> Eq[Nat, a, fib_recursive(n)]:
    # At exit: remaining = 0, so index = n and a = Fₙ.
    index_is_n = rewrite_in(counter_zero(remaining, test), inv.fst)
    return rewrite(sym(index_is_n), inv.snd.fst)


@verified(using=(add_zero, fib_preserve, fib_exit))
def fib_loop(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, fib_recursive(n)]]:
    # The Refined result requires a proof that the returned value equals Fₙ.
    remaining = n
    index = 0
    a, b = 0, 1
    while 0 < remaining:
        # The invariant ties loop state to the recursive specification.
        invariant(lambda remaining, index, a, b: FibInvariant(n, remaining, index, a, b), state=(remaining, index, a, b))
        # remaining decreases on every iteration, proving termination.
        decreases(remaining)
        a, b = b, a + b
        index = S(index)
        remaining = pred_or(0, remaining)
    return a


@theorem
def fib_loop_correct(n: Nat) -> Eq[Nat, fib_loop(n), fib_recursive(n)]:
    # The verified specification yields fib_loop(n) = Fₙ for every n.
    return verified_spec(fib_loop, n, MkUnit())


@theorem
def fib_loop_twice(n: Nat) -> Eq[Nat, add(fib_loop(n), fib_loop(n)), add(fib_recursive(n), fib_recursive(n))]:
    # Congruence lifts the equality through addition: x = y → x+x = y+y.
    return cong2[Nat, Nat, Nat](lambda x: lambda y: add(x, y), verified_spec(fib_loop, n, MkUnit()), verified_spec(fib_loop, n, MkUnit()))


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    print(f"fib(10) = {fib_loop(10)}")
