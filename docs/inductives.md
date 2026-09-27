# Inductive families and dependent pattern matching

## Checked declarations

A kernel `DataDecl` has parameter and index telescopes, a concrete universe, and one or more constructors. Each constructor declares fields and result indices. The kernel checks the family, constructors, and eliminator and registers the complete declaration atomically. Direct recursive fields and positive function-typed recursive fields receive induction hypotheses. NbE and elaboration use the same constructor reduction rules; neutral eliminations remain neutral.

Strict positivity is checked after unfolding type aliases. Negative and double-negative occurrences, changed recursive parameters, self-referential result indices, and constructor types using their own eliminator are rejected. Mutual inductives, nested recursion through an existing type constructor, and universe polymorphism are not accepted.

```python
from deppy import inductive, constructor, dependent, Type

@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent(decreases="xs")
def append[A: Type](xs: List[A], ys: List[A]) -> List[A]:
    match xs:
        case Nil():
            return ys
        case Cons(head, tail):
            return Cons(head, append(tail, ys))
```

Constructor names are public names in the checked module and must be unique. Type parameters may be explicit (`Cons[A](head, tail)`) or inferred. Indices follow parameters. `@inductive(level=1)` selects a concrete universe. Indexed families declare an index before constructors, for example `length: Index[Nat]`; each constructor supplies its result index, for example `IVec[A, S(k)]`. The index name in the class is not a constructor-local value. These declarations are parsed statically; their classes and decorators are never executed.

`induct(level, value, motive, *branches)` explicitly eliminates an inductive value. The motive receives indices and the value; each branch receives its fields followed by induction hypotheses for recursive fields. A function-typed recursive field yields a function-typed hypothesis. `absurd(type, value)` eliminates an empty family or an impossible constructor index determined by constructor mismatch; it does not solve arbitrary equality contradictions or unknown indices.

## Patterns and recursion

Ordered constructor patterns support nesting, captures, wildcards, nested matches, coverage, unreachable duplicate detection, arity checking, and nominal type checking. Recursive calls may use direct recursive fields, including multiple fields, and descendants obtained from nested matches when the induction history supplies their hypotheses. Later arguments may be generalized. Without explicit `decreases`, the first matched argument is structural. Function-typed recursive fields require explicit `induct`.

Fixed and compound indices may be matched when normalization yields a linear pattern of variables and constructors. Impossible branches caused by constructor mismatch may be omitted. Index-sensitive motives and context generalization support nested `IVec`/`IFin` lookup without casts or additional axioms.

Guards, keyword and OR patterns, arbitrary equality-driven branch search, and nonlinear or neutral function applications in index patterns are rejected. Existing built-in compatibility patterns retain their narrower rules; the general pattern matrix applies to `@inductive` families. Recursive calls must pass the structural checker; a mere syntactic self-call is not accepted as a termination proof.

## Standard data and runtime boundary

`deppy.data` supplies Empty, Unit, Bool, Sum, Option, Not, and Decidable. `deppy.lists` supplies List operations and the four general list theorems. `deppy.nat` supplies canonical Nat arithmetic; `deppy.indexed` supplies `IVec`, `IFin`, and safe `get` indexed by that Nat. Existing Nat, Vec, and Fin compatibility APIs also lower to checked general inductives; there are no dedicated Nat/Vec/Fin variants in trusted terms or NbE.

Generated inductive values use a nominal tag, constructor number, and immutable field tuple. The runtime validates constructor arity, dependent fields, available indices, and schemas for type parameters. Recursive schemas refer to finite declaration templates. Higher-order fields and function arguments receive wrappers that check arguments and results at each call. External callback termination is not proved. Public schema comparison is limited to representable indices; an index requiring erased types, proofs, or functions is rejected. External Python proof inputs are rejected.

## Interfaces and diagnostics

The frontend propagates source spans through elaboration. Diagnostics identify the source, location, related declaration, and expected/actual types where applicable. Duplicate or ill-typed patterns point to the pattern; nonexhaustive matches point to the match. Named holes have local-context goals, unique analysis IDs, and CLI `--goals` / `--json` output. An incomplete declaration is not registered; a module with diagnostics is not verified.

The read-only checked interface exposes declaration kinds, inductive and constructor metadata, aliases, record projections, and axiom dependencies with its kernel snapshot. `CheckSession::check` may reuse a dependency snapshot only when its source and options match. It rechecks the root and does not update its cache after a failed check. Source resolution, parsing, and lowering still run on each check. Processing budgets and Rust/Python stack limits apply.
