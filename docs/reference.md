# Core, frontend, and runtime reference

DepPy has two static frontends. `@dependent` elaborates total functions and proofs; `@verified` lowers a pure imperative subset to Verified HIR and generates verification conditions. Both produce dependent core terms checked by the same kernel. Mutable local state and control flow remain in Verified HIR, while checked verified specifications can be reused by dependent proofs. The runtime generator is an optional consumer of checked terms, not part of the proof-validity boundary.

## Core typing and conversion

`deppy-core` checks fully explicit, closed terms. It provides noncumulative concrete universes (`Type[0] : Type[1]`), Π and Σ types, typed lambda/application/let, de Bruijn binding, checked globals, equality and `J`, and strictly positive indexed inductive families. Records are nonrecursive, nominal, single-constructor inductives with generated dependent projections. Nat, Vec, and Fin are registered as ordinary checked inductives, while compatibility builders retain their existing surface API.

Normalization by evaluation uses closures and β, ζ, and constructor/eliminator ι reduction. Function η is part of typed equivalence; there is no general Σ η rule. `Kernel::infer`, `check`, `normalize`, and typed `equivalent` check their inputs before evaluation. The kernel rejects malformed terms and exhausted step budgets. Budgets limit computation steps, not all stack or memory use. Universe levels are `u32`; an unrepresentable successor is rejected.

`Kernel::erase` checks runtime uses after typing and projects checked terms to `RuntimeTerm`/`RuntimeType`. The optional runtime crate consumes that projection. `deppy-python::check_module` and `deppy-runtime::compile_module` are separate entry points. See [proof erasure](proofs.md#proof-erasure) for the conservative rule.

### Natural numbers and equality

Nat has `Z` and `S`. Its eliminator has this type:

```text
P    : Nat → Type[level]
zero : P Z
step : Π (k : Nat). P k → P (S k)
n    : Nat
──────────────────────────────────
NatElim(level, P, zero, step, n) : P n
```

It reduces at `Z` and `S(k)` and remains neutral on an unknown scrutinee. Addition is defined by induction on its first input: `add Z m ≡ m` and `add (S k) m ≡ S (add k m)`. `add n Z = n` for variable `n` needs a proof such as `zero_right`; it is not a definitional equality.

`Eq[A,x,y]` has `refl`; `J(level, A, x, C, d, y, p)` requires `C : (z : A) → Eq[A,x,z] → Type[level]` and `d : C(x,refl(x))`, then returns `C(y,p)`. It reduces when `p` is `refl` and stays neutral otherwise. Equality evidence does not itself make endpoints definitionally equal. Proof irrelevance, UIP/K, and function extensionality are not kernel rules. Library `sym`, `trans`, `cong`, and `transport` use `J`.

### Dependent pairs, vectors, and indices

`Sigma[A, lambda x: B]` forms a dependent pair; `Pair(a,b)` is checked against an expected Σ type, or `pair(SigmaType,a,b)` gives it explicitly. `fst` has type `A` and `snd` has type `B(fst)`. Pair projections reduce on a constructor and both components are checked, even if one is later discarded.

```text
VNil(A)              : Vec A Z
VCons(A, k, h, tail)  : Vec A (S k)    h : A, tail : Vec A k
FZ(k)                : Fin (S k)
FS(k, j)             : Fin (S k)      j : Fin k
```

The kernel checks every size witness. `Fin Z` has no constructor; `fin0_elim(A, impossible)` eliminates it. `VecElim` and `FinElim` take an explicit universe level, motive, branches, index, and scrutinee. The Vec motive is `(k : Nat) → Vec A k → Type[level]`; the Fin motive is `(k : Nat) → Fin k → Type[level]`. Their branches receive recursive induction hypotheses. `append` and safe `get` are ordinary eliminator definitions, with `get` using motive `Fin k → A` and `fin0_elim` in the empty case.

## Elaboration and definitions

`deppy-elab` converts named `Expr` values to explicit core. `Elaborator::infer` synthesizes types; `check` uses expected types to check unannotated lambdas. Application inserts leading implicit arguments, which may also be supplied with `Expr::implicit`. Metavariables retain their creation telescope and expected type; solving enforces occurs and scope checks. Only distinct-local-variable pattern unification is supported. Unsolved metavariables are rejected, including ones erased during reduction. Solutions and final pre-reduction core terms are rechecked by the kernel.

A local `let` is immutable, can be referenced in types, cannot refer to itself, and is checked even if unused. Globals are registered only after successful checking. Replacing an ID/name, self-reference, and forward reference are rejected. Transparent definitions unfold for conversion; `@dependent(opaque=True)` retains a checked body but does not unfold. Axioms have checked types and no bodies. Declaration IDs belong to one elaborator/kernel environment; use that same kernel for subsequent checks.

The standalone elaborator accepts Rust-built ASTs; `deppy-python` parses Python separately. It retains expression spans, although some structural errors identify only a declaration. The elaborator uses capture-avoiding substitution and weak-head reduction, distinct from the kernel's closure-based NbE. Keyword application, deferred constraints, and general higher-order unification are unsupported.

## Python frontend

`lower_module(source, Target)` parses Python 3.12, 3.13, or 3.14 with Ruff and returns declarations and UTF-8 byte ranges. `check_module` checks a fresh environment and returns checked definitions plus its elaborator, or fails without returning a partial checked module. The CLI defaults to Python 3.14 syntax and reports file, line, and column. The Ruff parser, AST, and text-size crates are pinned together at `=0.0.12`.

The dependent subset accepts `from __future__ import annotations`, static imports from checked `deppy` modules and local sources, annotated positional parameters and returns, implicit `[A: Type]` parameters, immutable local assignments, pure expressions, `return`, and structurally checked `match`/recursion. Constants may use `def name() -> A`. Supported expressions include `Type[level]`, dependent function and pair types, Nat/Vec/Fin/Eq constructors and eliminators, position-based application, explicit bracketed implicit arguments, and Nat literals. Built-in compatibility forms are illustrated by `crates/deppy-python/examples/core/basics.py` and `proofs.py`.

`@dependent(decreases="parameter", motive_level=0)` selects a structural argument and concrete result universe. Recursive calls must follow direct substructure and pass all parameters in order. General `@inductive` patterns have the rules in [inductive families](inductives.md); built-in compatibility patterns retain their specific restrictions. Pattern captures cannot shadow existing local or global names. Values defined before a match are checked in their original context and re-elaborated under a refined branch context; even unused bad definitions are rejected.

`@record` creates a nominal, nonrecursive, single-constructor record with typed fields. A field may depend on preceding fields (`self.n`), and selection (`r.value`) resolves against the receiver's nominal type. The default universe is 0; `@record(level=1)` selects another concrete level. Inheritance, methods, defaults, recursive records, and ambiguous receiver types are rejected. Use `@inductive` for recursive data.

The frontend rejects unsupported Python features rather than treating them as unchecked code: reassignment in `@dependent`, default/keyword/variadic parameters, arbitrary attribute access, effects, unverified recursion, and unsupported annotations. Undecorated functions and module-level assertions are parsed but not checked as DepPy proofs or included in generated exports. Static parsing is distinct from CPython execution or a general semantic-preservation theorem.

## Runtime interface

`deppy-runtime::compile_module(source, Target)` and its CLI generate a standalone Python module. Public names are called through `exports['name']`; implicit type arguments are omitted. Public functions validate argument/result schemas and rebuild immutable values. Higher-order boundaries wrap callbacks to check each call's arguments and result; callback termination is not established.

Repeat `--export NAME` to generate only selected root declarations and their runtime dependencies. Without this option, the CLI exports every root declaration. The library equivalent is `compile_exports_with_resolver(source, target, resolver, names)`. Selection happens after the entire module is checked, so an invalid unselected proof still rejects compilation. Unknown names are errors. This allows executable functions to be extracted from a module that also contains proofs with unsupported runtime uses of erased arguments.

| Checked value | Python boundary representation |
| --- | --- |
| Nat | Nonnegative `int`; `bool` rejected |
| Vec | Immutable tuple |
| Fin | `(bound, zero_based_index)` |
| Σ | Two-element tuple |
| Record / general inductive | Module-specific nominal tag, constructor number where relevant, immutable fields |
| Type | `None` |
| Equality proof | Internal token when needed; public result `None` |

The boundary checks Vec length, Fin bound, known element types, dependent fields, constructor arity, nominal tags, and representable indices. Mutable lists, forged tags, and wrong bounds are rejected. Erased type parameters are treated as opaque immutable data rather than checked against an original Python class. Proofs cannot enter from external Python, and a public schema that requires erased evidence or an arbitrary type family is rejected. Generated classes are not source-compatible with arbitrary Python record classes. Rust checking and generated Python calls remain subject to stack/memory limits.

```sh
cargo run -p deppy-runtime --locked --offline -- crates/deppy-python/examples/core/proofs.py > /tmp/deppy_proofs.py
uv run --no-project --offline --python 3.12 python -c "import runpy; f = runpy.run_path('/tmp/deppy_proofs.py')['exports']; print(f['get'](3, (10, 20, 30), (3, 1)))"
```

`CheckSession` can reuse checked dependency snapshots for identical sources and options; the root module is checked again. Changes to dependencies invalidate their snapshots. `FrontendOptions` selects the Python target and processing budgets. `CheckedModule.interface` exposes checked names, declaration kinds, constructors, axiom dependencies, and the associated kernel snapshot. Serialized interfaces do not bypass checking.

`hole("name")` and `analyze_module` expose goals with local context and source spans. A module with unresolved goals or diagnostics has no `CheckedModule`. Run `deppy-python --goals file.py` or `--json file.py` to inspect it. See [development and verification](development.md) for checks and their limits.
