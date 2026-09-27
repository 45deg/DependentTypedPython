# Verified programs

`@verified` statically checks a pure imperative subset over Nat, Bool, and Int. It accepts local assignments, branches, multiple or nested `while` loops, Nat-bounded `for range`, `continue`, `break`, and `return`. The frontend builds Verified HIR, generates verification conditions (VCs), and checks their proofs as ordinary dependent core terms. Decorators and annotations are parsed, not run as CPython code. A function with unresolved VCs is not registered as verified.

```python
from deppy import Nat, Eq
from deppy.nat import add
from deppy.verified import verified, Refined

@verified
def twice(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, add(n, n)]]:
    x = n
    x = x + n
    return x
```

## Contracts and refinements

`@verified` or `@verified()` attempts bounded automatic proof. `Refined[Base, predicate]` accepts only `Nat`, `Bool`, or `Int` as `Base`. A parameter predicate receives its value and may refer to earlier parameter entry values. It cannot refer to itself by the outer parameter name or to later parameters. A return predicate receives the result and may refer to all parameter entry values. Reassigning an argument in the body does not change those captured entry values. A refined return replaces `ensures`; specifying both is rejected. The public function still returns its base value, not a Σ wrapper.

`requires` takes the input parameters in declaration order and returns a proposition. `ensures` takes the input parameters and then the result and returns a proposition. Refined parameter predicates, followed by explicit `requires`, form the precondition. With no conditions it is `Unit`; with one it is that condition directly; with several it is a right-associated Σ. Its evidence is the `pre` argument to proof callbacks and the final argument to `verified_spec`. If a plain base return has no `ensures`, its postcondition is `Unit`, so no stronger result property is claimed.

A local `x: Refined[Base, predicate] = value` creates an assignment VC for the initial value and each later assignment, including simultaneous assignment. The predicate's free variables are captured at annotation time. Reannotating `x` with its base type does not remove the condition; redeclaring a refinement for the same local is rejected. A conversion between predicates on the same base type requires proof at the assignment or callee precondition VC. There is no implicit refinement subtyping or cross-base conversion.

| Goal key | Obligation |
| --- | --- |
| `local.x.refined`, `local.x.2.refined` | First and subsequent assignments preserve `x`'s predicate |
| `then.local.x.refined` | Predicate on a branch assignment |
| `call.y.requires`, `call.y.2.requires` | First and subsequent calls assigned to `y` prove the callee precondition |
| `call.return.requires` | A returned call proves its precondition |
| `return`, `then.return`, `else.return` | Path-specific postcondition |
| `assert.test.holds`, `assert.test.2.holds` | An assertion evaluates to Bool true |
| `arithmetic.sub.safe`, `arithmetic.div.safe`, `arithmetic.mod.safe` | Numeric operation safety |

Nested path names concatenate, for example `then.else.call.y.requires`. Function names prefix displayed goals. A normalized expression call uses `call.$exprN.requires`; numbering depends on lowering, so inspect `--goals` before supplying a proof. Goal source locations point to the original expression. Duplicate, unknown, or unused `proofs` keys are rejected.

## Proof selection and contract calls

Automatic proof can use context evidence and Σ projections, reflexivity, Unit/Σ construction, fixed natural-order lemmas, and comparisons known to be true or false. Search and Σ depth are bounded. It is not a general arithmetic solver and does not search arbitrary user theorems or axioms. `@verified(using=(lemma1, lemma2))` adds already checked declarations to one-step matching against VCs, solving their premises from context evidence or reflexivity. Imported aliases work. Explicit `proofs={...}` take priority; unused or unsolved goals remain visible. `using` cannot be combined with `auto=False` or a single `proof=`. Axiom dependencies of proofs actually used are tracked.

`proof=` is a single dependent proof callback receiving inputs and precondition evidence. It cannot be combined with `proofs`. Without loops it proves the whole postcondition; its special single-loop form is described below. `proofs={key: callback}` supplies individual VCs. Every supplied proof is checked even if automatic proof could have solved that VC; an incorrect proof is never replaced. `@verified(auto=False)` disables automatic proof and displays all unspecified goals. `--goals` and `--json` expose names, types, context, and locations. A `hole` in any proof keeps the module incomplete.

A verified callee can be used in assignments, returns, expression arguments, arithmetic, branch conditions, conditional expressions, simultaneous-assignment right sides, loop initialization/body, and after a loop. Arguments are evaluated left to right; all right sides of simultaneous assignment use the old state before targets change. Every call proves its precondition. The continuation is checked for an abstract result satisfying the callee's opaque postcondition, and only then instantiated with the actual result and `verified_spec`. The caller cannot establish the continuation by unfolding the callee's implementation. Import aliases and reexports preserve contracts and axiom dependencies. Calls in a `while` guard are unsupported. The single `proof=` path cannot call a verified function as an ordinary pure function.

A proof callback receives entry inputs, precondition evidence, then path evidence in order. Each call contributes an abstract result and postcondition evidence; each branch contributes equality of its Bool condition to true or false. Ordinary assignments add no callback argument. Old call evidence continues to refer to the old value after reassignment. Callbacks must be positional lambdas or checked lemmas applicable in that order.

## Expressions, arithmetic, and control flow

The base types are public `Nat`, `deppy.data.Bool`, and `deppy.integer.Int`. Nat is nonnegative. Int is an inductive signed representation: `Pos(n)` denotes `n`, `Neg(n)` denotes `-(n+1)`, so there is no negative zero. Nat and Int values do not mix implicitly. `of_nat` converts Nat to Int; `to_nat` is a verified contract call requiring nonnegativity.

Accepted values include initialized locals, integer and Bool literals, `+`, `-`, `*`, `//`, `%`, Int unary minus, comparisons, Bool `and`/`or`/`not`, conditional expressions, and positional calls to previously checked pure dependent or verified functions. Bool `and` and `or` short circuit and produce Bool values, not general Python operand values. A conditional expression checks only its reached branch. `assert p` proves `Eq[Bool,p,True_()]` and adds that evidence to the following context. Assertions with messages are unsupported.

| Program expression | Specification function or proposition |
| --- | --- |
| `n < m`, `n <= m` | `nat_lt(n,m)`, `nat_le(n,m)`; a true decision yields `LT` or `LE` |
| `n > m`, `n >= m` | `nat_lt(m,n)`, `nat_le(m,n)` |
| Nat `n == m`, Bool `a == b` | `nat_eq(n,m)`, `bool_eq(a,b)` |
| `a != b`, `not a` | Bool negation of equality, `bool_not(a)` |
| `x if p else y` | Branch on Bool `p` |

These functions and lemmas are in `deppy.verified`. Specification annotations use dependent expressions such as `add(n,1)` or `LE[n,limit]`; program operators are not automatically general proposition syntax.

Nat `a - b` requires a proof of `b <= a`; program subtraction does not silently use the saturating total `deppy.arithmetic.sub`. Nat `a // b` and `a % b` require `0 < b`. Int division and remainder require a nonzero divisor and follow floor division: `-7 // 3 = -3`, `-7 % 3 = 2`, `7 // -3 = -3`, `7 % -3 = -2`. Remainder takes the divisor's sign. Int subtraction has no Nat-style lower-bound VC. A positive literal is Int when an Int type is expected and Nat otherwise; a negative literal is Int. Augmented `+=`, `-=`, `*=`, `//=`, and `%=` obey the same safety and refinement rules. Safety VCs occur only on reachable short-circuit/conditional paths and use the old state for simultaneous assignment. Unsafe arithmetic is unsupported in `while` guards, direct decreases expressions, and the single `proof=` path; compute it into a checked local first.

A new local derives its fixed type from its right side. If a pure call has no expected type or known Int contract/operator to determine its result, it is checked as Nat; annotate a new Bool local explicitly. Simultaneous assignment requires distinct names in a flat tuple and an equally sized tuple expression. Nested/starred targets and duplicate names are rejected. A first docstring is allowed. General expression statements, heap mutation, exceptions, I/O, async, type parameters, default/keyword arguments, attributes, recursion, and implicit `None` returns are outside the subset.

HIR maps each local to its type and a fresh core binding. An assignment evaluates in the old state and updates the binding; a branch uses a Bool eliminator and path-specific states; a return stops that path. A path falling through without return or using an uninitialized variable is rejected. For loop-free bodies with semantic function `D(inputs)` and postcondition `Q`, the overall VC is `Π inputs. requires(inputs) → Q(inputs,D(inputs))`. Checked proof lets and `D` reside in the final core definition, so unused invalid proofs are still rejected. The guarantee applies to this HIR semantics; general equivalence with original CPython execution is not established.

## Loops and termination

A `while` loop needs an invariant and a Nat-valued decreasing measure. If `invariant` is omitted, variables assigned in the body become state in first-use order; their local `Refined` predicates form an invariant candidate (Unit for none, the predicate for one, right-associated Σ for several). Initialization and preservation must be proved before that candidate is used. Parameter refinements are entry preconditions, not automatically invariants after parameter reassignment. All state variables must be initialized before the loop. Explicit annotations go at the beginning of the body:

```python
while 0 < counter:
    invariant(lambda counter, total: Eq[Nat, add(counter, total), n],
              state=(counter, total))
    decreases(lambda counter, total: counter)
    total = S(total)
    counter = pred_or(0, counter)
```

`invariant` and `decreases` come from `deppy.verified_loop`. Their lambda arguments are current state values in `state` order; other captured values come from loop entry. `decreases(counter)` also denotes the current value of that state variable. State may mix Nat, Bool, and Int but types cannot change during iteration. The body may assign only state variables; inner-loop state must also be in outer state. A nonstate local is read-only during that loop. `while ... else` and `for ... else` are rejected.

For a simple function-level single `while`, `proof=` may return a nested `Pair` of four proofs: initialization, preservation, strict decrease, and exit postcondition. The named equivalent is `loop.init`, `loop.preserve`, `loop.decrease`, `loop.exit`. Preservation and decrease callbacks receive state, invariant evidence, and guard-true evidence; exit receives guard-false evidence. The state proof shape ends with Unit, for example two Nat fields form `Sigma[Nat, lambda _: Sigma[Nat, lambda _: Unit]]`. The four proofs are assembled with the checked `loop_correct` library theorem.

Automatic proof or `proofs` handles multiple, nested, and branch-local loops, branches before loops, `continue`, `break`, and return inside a loop. Loop numbers follow source order, starting at one and counting outer loops before inner loops. Composite keys include paths, for example `loop.1.step.preserve`, `loop.1.step.then.decrease`, `loop.1.step.loop.2.init`, and `loop.1.exit.return`. A following loop may use the previous loop's invariant and guard-false evidence. `continue` skips to the innermost next iteration and must prove invariant preservation and strict decrease at that point. `break` leaves only the innermost loop; it checks the continuation from that state without assuming the guard false or requiring another iteration's decrease. A return inside a loop proves the function postcondition at that point. Normal iteration, break, and return are separated in checked Sum/Σ results. A measure can be zero on an immediate break or return path.

`for range` accepts `range(stop)`, `range(start, stop)`, and `range(start, stop, step)` with Nat bounds and an exclusive stop. The default step is 1; a positive Nat expression ascends and a negative integer literal descends. Zero step is rejected even for an empty range. A dynamic step must prove positive magnitude at `range.step.positive`. General Int bounds, dynamic negative steps, Bool/float arguments, keyword arguments, shadowed `range`, and `for ... else` are rejected. The target must be an already initialized Nat local. An empty range leaves its entry value intact.

Bounds and step are evaluated once, left to right, including their contract calls. Changes to a bound local or target in the body do not alter the selected range. `continue` advances the iteration; `break` and `return` use the usual early-exit proof routes. An optional `invariant(..., state=(...))` lists the target and modified user locals; internal cursor/count state is supplied automatically, and no user `decreases` is needed. Finite iteration and while correctness use checked structural-recursion lemmas. Lexicographic measures, arbitrary well-founded relations, and general invariant inference are unsupported. Processing budgets can limit deeply branched VC generation.

## Reusing a verified specification

```python
from deppy.verified import verified_spec
from deppy.data import MkUnit

@theorem
def twice_spec(n: Nat) -> Eq[Nat, twice(n), add(n, n)]:
    return verified_spec(twice, n, MkUnit())
```

`verified_spec(f, *inputs, precondition_proof)` applies the opaque checked theorem associated with a statically resolved verified function. Its type is `Π inputs. requires(inputs) → ensures(inputs,f(inputs))`. A missing precondition uses `MkUnit()`; a real precondition requires its actual evidence. Partial application returns a proof function for remaining inputs. An ordinary dependent function, local variable, or arbitrary expression cannot replace `f`. Aliases and reexports resolve to the original checked function. The theorem body, type, and opacity live in the checked interface's kernel snapshot; changing function source or options invalidates dependent snapshots. Axiom dependencies propagate through reuse.

The [Fibonacci example](../crates/deppy-python/examples/verified/fibonacci.py) checks a loop result against a structurally recursive Fibonacci specification. It uses a simultaneous update, an invariant relating index and consecutive values, a decreasing remaining count, and explicit `using` lemmas. Later theorems reuse its `verified_spec`. This checks the HIR function and its VC proof; it is not a runtime benchmark or CPython semantic-preservation proof.
