from deppy import dependent, theorem, record, Type, Pi, Sigma, Pair, Nat, Z, S, Fin, FZ, FS, Vec, VNil, VCons, Eq, refl, absurd, fin0_elim
from deppy.bool import Bool, False_, True_, is_true, conjunction, disjunction
from deppy.data import Sum, Left, Right, sum_elim, MkUnit
from deppy.fin import fin_case
from deppy.vectors import get
from deppy.equality import transport, sym
from deppy.lists import List, Nil, Cons


# Part 7: every epsilon-free NFA can be converted to an equivalent DFA.
#
# NFA acceptance means that an actual path exists (Path / FromSet).
# DFA acceptance is a Boolean computation (dfa_from / dfa_accepts).
# determinize_correct proves both implications for EVERY input word.
#
# The subset construction uses Vec[Bool, n] as its state space: one bit
# for each NFA state. Thus the resulting automaton has a finite state
# space (2^n possible bit vectors), even though not all are reachable.
# Initial states may form a set; a single initial state is a special case.
# There are no epsilon transitions: each edge consumes one input symbol.
#
# Reading order: NFA / DFA, Path, determinize, determinize_correct,
# then the branching example at the bottom. The helpers are included
# here so every step of the proof can be edited and checked in this demo.


# Boolean logic and finite search: turn a successful search into a witness,
# and prove that any witness makes the search succeed.


@theorem
def and_intro(a: Bool, b: Bool, pa: is_true(a), pb: is_true(b)) -> is_true(conjunction(a, b)):
    match a:
        case False_():
            return absurd(is_true(conjunction(False_(), b)), pa)
        case True_():
            return pb


@theorem
def and_split(a: Bool, b: Bool, proof: is_true(conjunction(a, b))) -> Sigma[is_true(a), lambda _: is_true(b)]:
    match a:
        case False_():
            return absurd(Sigma[is_true(False_()), lambda _: is_true(b)], proof)
        case True_():
            return Pair(MkUnit(), proof)


@theorem
def or_left(a: Bool, b: Bool, proof: is_true(a)) -> is_true(disjunction(a, b)):
    match a:
        case False_():
            return absurd(is_true(disjunction(False_(), b)), proof)
        case True_():
            return MkUnit()


@theorem
def or_right(a: Bool, b: Bool, proof: is_true(b)) -> is_true(disjunction(a, b)):
    match a:
        case False_():
            return proof
        case True_():
            return MkUnit()


@theorem
def or_split(a: Bool, b: Bool, proof: is_true(disjunction(a, b))) -> Sum[is_true(a), is_true(b)]:
    match a:
        case False_():
            return Right(proof)
        case True_():
            return Left(MkUnit())


@dependent(decreases="n")
def some(n: Nat) -> Pi[Pi[Fin[n], lambda q: Bool], lambda predicate: Bool]:
    match n:
        case Z():
            return lambda predicate: False_()
        case S(k):
            return lambda predicate: disjunction(predicate(FZ(k)), some(k)(lambda q: predicate(FS(k, q))))


@dependent
def lift_witness(k: Nat, predicate: Pi[Fin[S(k)], lambda q: Bool], witness: Sigma[Fin[k], lambda q: is_true(predicate(FS(k, q)))]) -> Sigma[Fin[S(k)], lambda q: is_true(predicate(q))]:
    return Pair(FS(k, witness.fst), witness.snd)


@theorem(decreases="n")
def some_sound(n: Nat) -> Pi[Pi[Fin[n], lambda q: Bool], lambda predicate: Pi[
    is_true(some(n)(predicate)), lambda proof: Sigma[Fin[n], lambda q: is_true(predicate(q))]
]]:
    match n:
        case Z():
            return lambda predicate: lambda proof: absurd(Sigma[Fin[0], lambda q: is_true(predicate(q))], proof)
        case S(k):
            return lambda predicate: lambda proof: sum_elim[is_true(predicate(FZ(k))), is_true(some(k)(lambda q: predicate(FS(k, q)))), Sigma[Fin[S(k)], lambda q: is_true(predicate(q))]](
                or_split(predicate(FZ(k)), some(k)(lambda q: predicate(FS(k, q))), proof),
                lambda first: Pair(FZ(k), first),
                lambda rest: lift_witness(k, predicate, some_sound(k)(lambda q: predicate(FS(k, q)))(rest)),
            )


@theorem(decreases="n")
def some_complete(n: Nat) -> Pi[Pi[Fin[n], lambda q: Bool], lambda predicate: Pi[
    Sigma[Fin[n], lambda q: is_true(predicate(q))], lambda witness: is_true(some(n)(predicate))
]]:
    match n:
        case Z():
            return lambda predicate: lambda witness: fin0_elim(witness.fst)
        case S(k):
            return lambda predicate: lambda witness: fin_case(
                k, lambda q: Pi[is_true(predicate(q)), lambda proof: is_true(some(S(k))(predicate))], witness.fst,
                lambda proof: or_left(predicate(FZ(k)), some(k)(lambda q: predicate(FS(k, q))), proof),
                lambda q: lambda proof: or_right(predicate(FZ(k)), some(k)(lambda r: predicate(FS(k, r))),
                    some_complete(k)(lambda r: predicate(FS(k, r)))(Pair(q, proof))),
            )(witness.snd)


# Build a subset bit vector from its membership test.
# tabulate_get proves that looking up bit q recovers that test at q.


@dependent(decreases="n")
def tabulate(n: Nat) -> Pi[Pi[Fin[n], lambda q: Bool], lambda predicate: Vec[Bool, n]]:
    match n:
        case Z():
            return lambda predicate: VNil()
        case S(k):
            return lambda predicate: VCons(k, predicate(FZ(k)), tabulate(k)(lambda q: predicate(FS(k, q))))


@theorem(decreases="n")
def tabulate_get(n: Nat) -> Pi[Pi[Fin[n], lambda q: Bool], lambda predicate: Pi[
    Fin[n], lambda q: Eq[Bool, get(n, tabulate(n)(predicate), q), predicate(q)]
]]:
    match n:
        case Z():
            return lambda predicate: lambda q: fin0_elim(q)
        case S(k):
            return lambda predicate: lambda q: fin_case(
                k, lambda r: Eq[Bool, get(S(k), tabulate(S(k))(predicate), r), predicate(r)], q,
                refl(predicate(FZ(k))),
                lambda r: tabulate_get(k)(lambda t: predicate(FS(k, t)))(r),
            )


# Automata. NFA edges are a relation, so a symbol may have zero, one,
# or several successors. DFA transitions return exactly one state.


@record
class NFA[A: Type, n: Nat]:
    initial: Vec[Bool, n]
    edge: Pi[Fin[n], lambda q: Pi[A, lambda symbol: Pi[Fin[n], lambda r: Bool]]]
    final: Pi[Fin[n], lambda q: Bool]


@record
class DFA[A: Type, Q: Type]:
    start: Q
    step: Pi[Q, lambda state: Pi[A, lambda symbol: Q]]
    final: Pi[Q, lambda state: Bool]


@dependent(decreases="word", motive_level=1)
def Path[A: Type, n: Nat](machine: NFA[A, n], word: List[A]) -> Pi[Fin[n], lambda q: Type]:
    # Empty word: q must be final. Nonempty word: choose a successor r,
    # provide evidence of the edge, and an accepting path for the tail.
    match word:
        case Nil():
            return lambda q: is_true(machine.final(q))
        case Cons(symbol, tail):
            return lambda q: Sigma[Fin[n], lambda r: Sigma[
                is_true(machine.edge(q)(symbol)(r)), lambda edge: Path(machine, tail)(r)
            ]]


@dependent
def FromSet[A: Type, n: Nat](machine: NFA[A, n], word: List[A], subset: Vec[Bool, n]) -> Type:
    # An accepting path starts at SOME state belonging to the subset.
    return Sigma[Fin[n], lambda q: Sigma[is_true(get(n, subset, q)), lambda member: Path(machine, word)(q)]]


@dependent
def targets[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], symbol: A) -> Pi[Fin[n], lambda r: Bool]:
    # r belongs to the next subset iff some active q has an edge to r.
    return lambda r: some(n)(lambda q: conjunction(get(n, subset, q), machine.edge(q)(symbol)(r)))


@dependent
def advance[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], symbol: A) -> Vec[Bool, n]:
    return tabulate(n)(targets[A, n](machine, subset, symbol))


@dependent
def final_flags[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n]) -> Pi[Fin[n], lambda q: Bool]:
    return lambda q: conjunction(get(n, subset, q), machine.final(q))


@dependent
def finish[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n]) -> Bool:
    # A subset is accepting iff it contains an accepting NFA state.
    return some(n)(final_flags[A, n](machine, subset))


@dependent
def determinize[A: Type, n: Nat](machine: NFA[A, n]) -> DFA[A, Vec[Bool, n]]:
    # The empty subset is also a state; it transitions back to itself.
    return DFA[A, Vec[Bool, n]](
        machine.initial,
        lambda subset: lambda symbol: advance[A, n](machine, subset, symbol),
        lambda subset: finish[A, n](machine, subset),
    )


@dependent(decreases="word")
def dfa_from[A: Type, Q: Type](machine: DFA[A, Q], word: List[A]) -> Pi[Q, lambda state: Bool]:
    match word:
        case Nil():
            return lambda state: machine.final(state)
        case Cons(symbol, tail):
            return lambda state: dfa_from(machine, tail)(machine.step(state)(symbol))


@dependent
def dfa_accepts[A: Type, Q: Type](machine: DFA[A, Q], word: List[A]) -> Bool:
    return dfa_from(machine, word)(machine.start)


# One-step correspondence: a bit in the next subset is true exactly
# when there is a predecessor in the old subset with the required edge.


@theorem
def advance_complete[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], symbol: A, r: Fin[n],
    witness: Sigma[Fin[n], lambda q: Sigma[is_true(get(n, subset, q)), lambda member: is_true(machine.edge(q)(symbol)(r))]]
) -> is_true(get(n, advance(machine, subset, symbol), r)):
    return transport(is_true, sym(tabulate_get(n)(targets(machine, subset, symbol))(r)),
        some_complete(n)(lambda q: conjunction(get(n, subset, q), machine.edge(q)(symbol)(r)))(Pair(
            witness.fst, and_intro(get(n, subset, witness.fst), machine.edge(witness.fst)(symbol)(r), witness.snd.fst, witness.snd.snd)
        )))


@theorem
def advance_sound[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], symbol: A, r: Fin[n],
    proof: is_true(get(n, advance(machine, subset, symbol), r))
) -> Sigma[Fin[n], lambda q: Sigma[is_true(get(n, subset, q)), lambda member: is_true(machine.edge(q)(symbol)(r))]]:
    witness = some_sound(n)(lambda q: conjunction(get(n, subset, q), machine.edge(q)(symbol)(r)))(
        transport(is_true, tabulate_get(n)(targets(machine, subset, symbol))(r), proof)
    )
    return Pair(witness.fst, and_split(get(n, subset, witness.fst), machine.edge(witness.fst)(symbol)(r), witness.snd))


@theorem
def finish_complete[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], proof: FromSet(machine, Nil[A](), subset)) -> is_true(finish(machine, subset)):
    return some_complete(n)(final_flags(machine, subset))(Pair(proof.fst,
        and_intro(get(n, subset, proof.fst), machine.final(proof.fst), proof.snd.fst, proof.snd.snd)))


@theorem
def finish_sound[A: Type, n: Nat](machine: NFA[A, n], subset: Vec[Bool, n], proof: is_true(finish(machine, subset))) -> FromSet(machine, Nil[A](), subset):
    witness = some_sound(n)(final_flags(machine, subset))(proof)
    return Pair(witness.fst, and_split(get(n, subset, witness.fst), machine.final(witness.fst), witness.snd))


# Consume / reconstruct the first edge of an accepting NFA path.


@theorem
def path_step[A: Type, n: Nat](machine: NFA[A, n], symbol: A, tail: List[A], subset: Vec[Bool, n],
    proof: FromSet(machine, Cons(symbol, tail), subset)
) -> FromSet(machine, tail, advance(machine, subset, symbol)):
    return Pair(proof.snd.snd.fst, Pair(
        advance_complete(machine, subset, symbol, proof.snd.snd.fst, Pair(proof.fst, Pair(proof.snd.fst, proof.snd.snd.snd.fst))),
        proof.snd.snd.snd.snd,
    ))


@theorem
def path_unstep[A: Type, n: Nat](machine: NFA[A, n], symbol: A, tail: List[A], subset: Vec[Bool, n],
    proof: FromSet(machine, tail, advance(machine, subset, symbol))
) -> FromSet(machine, Cons(symbol, tail), subset):
    previous = advance_sound(machine, subset, symbol, proof.fst, proof.snd.fst)
    return Pair(previous.fst, Pair(previous.snd.fst, Pair(proof.fst, Pair(previous.snd.snd, proof.snd.snd))))


# Induction on the word, strengthened to ANY starting subset.
# Base: finite search of final states. Step: the one-edge correspondence
# reduces the statement to the induction hypothesis on the remaining word.


@theorem(decreases="word")
def nfa_to_dfa[A: Type, n: Nat](machine: NFA[A, n], word: List[A]) -> Pi[Vec[Bool, n], lambda subset: Pi[
    FromSet(machine, word, subset), lambda path: is_true(dfa_from(determinize(machine), word)(subset))
]]:
    match word:
        case Nil():
            return lambda subset: lambda path: finish_complete(machine, subset, path)
        case Cons(symbol, tail):
            return lambda subset: lambda path: nfa_to_dfa(machine, tail)(advance(machine, subset, symbol))(
                path_step(machine, symbol, tail, subset, path))


@theorem(decreases="word")
def dfa_to_nfa[A: Type, n: Nat](machine: NFA[A, n], word: List[A]) -> Pi[Vec[Bool, n], lambda subset: Pi[
    is_true(dfa_from(determinize(machine), word)(subset)), lambda accepted: FromSet(machine, word, subset)
]]:
    match word:
        case Nil():
            return lambda subset: lambda accepted: finish_sound(machine, subset, accepted)
        case Cons(symbol, tail):
            return lambda subset: lambda accepted: path_unstep(machine, symbol, tail, subset,
                dfa_to_nfa(machine, tail)(advance(machine, subset, symbol))(accepted))


@record
class Iff[P: Type, Q: Type]:
    forward: Pi[P, lambda proof: Q]
    backward: Pi[Q, lambda proof: P]


# Main theorem: specializing the two directions to the initial subset
# proves that the input NFA and the constructed DFA accept the same words.
# Iff stores both proof functions; neither implication is assumed.


@theorem
def determinize_correct[A: Type, n: Nat](machine: NFA[A, n], word: List[A]) -> Iff[
    FromSet(machine, word, machine.initial), is_true(dfa_accepts(determinize(machine), word))
]:
    return Iff(
        nfa_to_dfa(machine, word)(machine.initial),
        dfa_to_nfa(machine, word)(machine.initial),
    )


# Example: (0|1)*1 over {0, 1}, encoded as False_() / True_().
# q0 is initial and loops on both symbols. On 1, q0 can ALSO enter q1.
# q1 is final and has no outgoing edges. A branch must guess the last 1.
# Determinization keeps both branches in the subset {q0, q1} after a 1.


@dependent
def ends_in_one() -> NFA[Bool, 2]:
    return NFA[Bool, 2](
        VCons(1, True_(), VCons(0, False_(), VNil())),
        lambda q: lambda symbol: lambda r: fin_case(
            1, lambda state: Bool, q,
            fin_case(1, lambda state: Bool, r, True_(), lambda state: symbol),
            lambda state: False_(),
        ),
        lambda q: fin_case(1, lambda state: Bool, q, False_(), lambda state: True_()),
    )


@dependent
def empty_rejected() -> Eq[Bool, dfa_accepts(determinize(ends_in_one()), Nil[Bool]()), False_()]:
    return refl(False_())


@dependent
def one_accepted() -> Eq[Bool, dfa_accepts(determinize(ends_in_one()), Cons(True_(), Nil[Bool]())), True_()]:
    return refl(True_())


@dependent
def one_zero_rejected() -> Eq[Bool, dfa_accepts(determinize(ends_in_one()), Cons(True_(), Cons(False_(), Nil[Bool]()))), False_()]:
    return refl(False_())


@dependent
def zero_one_accepted() -> Eq[Bool, dfa_accepts(determinize(ends_in_one()), Cons(False_(), Cons(True_(), Nil[Bool]()))), True_()]:
    return refl(True_())


@dependent
def both_branches_kept() -> Eq[
    Vec[Bool, 2], advance(ends_in_one(), ends_in_one().initial, True_()),
    VCons(1, True_(), VCons(0, True_(), VNil()))
]:
    return refl(VCons(1, True_(), VCons(0, True_(), VNil())))


@dependent
def empty_subset_stays_empty() -> Eq[
    Vec[Bool, 2], advance(ends_in_one(), VCons(1, False_(), VCons(0, False_(), VNil())), True_()),
    VCons(1, False_(), VCons(0, False_(), VNil()))
]:
    return refl(VCons(1, False_(), VCons(0, False_(), VNil())))


@theorem
def one_has_nfa_path() -> FromSet(ends_in_one(), Cons(True_(), Nil[Bool]()), ends_in_one().initial):
    # Recover an NFA path from the computed DFA acceptance of [1].
    return determinize_correct(ends_in_one(), Cons(True_(), Nil[Bool]())).backward(MkUnit())


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    # Compare the computed DFA result for words ending in 1.
    # An accepting result also lets the checked backward theorem recover
    # an NFA path; the printed booleans alone do not prove equivalence.
    machine = ends_in_one()
    dfa = determinize[Bool, 2](machine)
    for bits in ((), (1,), (1, 0), (0, 1), (1, 1)):
        word = Nil[Bool]()
        for bit in reversed(bits):
            word = Cons(True_() if bit else False_(), word)
        accepted = bool(dfa_accepts(dfa, word))
        print(f"word {list(bits)}: accepted = {accepted}")
    print(f"after [1], subset = {advance[Bool, 2](machine, machine.initial, True_())}")
