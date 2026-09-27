# Standard-library gaps and extension plan

This plan compares the registered library with its source, tests, and proof examples. Items below are proposals, not accepted language features. Priority reflects reuse and dependency order: P0 resolves API ambiguity, P1 fills foundational gaps, and P2 promotes larger mathematical developments.

## Implemented baseline

The registry in [registry.rs](../crates/deppy-python/src/modules/registry.rs) supplies the `deppy` prelude directly and registers bundled Python source modules, including the compiler declarations in `deppy._builtins` and `deppy.tactics`. Removed Python prelude shims are not missing runtime packages: imports are resolved by the checked frontend.

| Area | Already available | Remaining gap |
| --- | --- | --- |
| Equality and logical data | `sym`, `trans`, congruence, transport; `Empty`, `Unit`, `Sum`, `Option`, `Decidable`; logical decisions | Operations and laws for `Option`; reusable equality decisions across carriers |
| Bool | Boolean operations, algebraic laws, constructive equality, truth evidence | Consolidate overlapping helpers in `verified`; add explicit bridges between Boolean tests and decisions |
| Nat and order | Add/multiply laws including commutativity, associativity and both distributivities; order decisions, totality, positive-factor cancellation, strong induction | Constructive equality API, min/max, reusable power and divisibility APIs |
| Natural arithmetic | Truncated subtraction; quotient/remainder computation, equation and remainder bound | Clarify direct-call versus verified-operator preconditions; additional reusable arithmetic laws |
| Int | Canonical signed representation, arithmetic, Boolean comparisons, floor division, conversion, `eq_true` | General algebra/order laws, constructive decisions, signed quotient/remainder theorems |
| Lists | Append/map/reverse and laws; membership, `NoDup`, `All`, `Any`, search, filter/count, removal | Folds, safe lookup, zip, take/drop, reusable elementwise equality |
| Fin and Vec | Fin-to-Nat bounds/injectivity; vector lookup/map/append/reverse, extensionality | Bound-checked Fin construction, enumeration, vector tabulation/update and List conversions |
| Finite carriers | `Enumeration`, finite quantifier decisions/search/count, transport by bijection | Standard enumerations, equality decision promoted from examples, closure constructions |
| Functions and permutations | Bijection identity/inverse/composition and laws; permutation equivalence, length/membership/`NoDup`/map preservation | General injective/surjective predicates; append/reverse/filter/fold permutation laws |
| Verified support | Branch evidence, loop correctness and range obligations | Keep compiler-facing obligations distinct from general-purpose math APIs |

Source locations: [stdlib](../crates/deppy-python/stdlib/deppy), [library integration tests](../crates/deppy-python/tests/libraries.rs), [numeric tests](../crates/deppy-python/tests/verified_numeric.rs). Existing checking and normalization tests do not imply complete extracted-runtime coverage.

## P0: establish one public vocabulary

1. **Share removal evidence.** `lists.py` and `finite.py` each declare `Removal`, `RemoveHere`, `RemoveThere`, and `find_removal`. These are separate nominal families despite having matching shapes. Keep the family in `deppy.lists`, port finite-specific laws to it, and reexport compatibility names from `deppy.finite`. Migrate the proof examples together. Acceptance: a `lists.Removal` proof works with finite removal/count laws, and Lagrange/Fermat clients still check.
2. **Keep foundational types shared across inductive demonstrations.** `deppy.indexed.IVec` and `IFin` use the canonical `deppy.nat.Nat`. New reusable APIs should use the canonical Nat/Fin/Vec families. Keep tests that exercise general inductives.
3. **Consolidate duplicate computations without changing conversion accidentally.** `bool.negate` overlaps with `verified.bool_not`; `arithmetic.equal` and `verified.nat_eq` compare naturals using different algorithms. Put general Boolean/decision bridges below verified-program support, retain compiler-referenced declarations as wrappers, and test neutral conversion as well as concrete normalization and existing proof clients. Preserve both Nat algorithms in P0 and prove a pointwise bridge. Avoid introducing a cycle between arithmetic, order, and verified modules. Do not turn computational definitions opaque merely to standardize decorators.
4. **Define the supported export surface.** The module loader currently reexports imports and declarations; underscore names are not a privacy mechanism. Helpers such as `case_motive`, `*_head`, and compatibility aliases therefore remain importable. First document curated public names; introduce facade/internal modules only with an explicit compatibility policy. Do not assume Python `__all__` controls checked imports.
5. **Complete API documentation.** The module overview and generated API have different coverage. `math-api.rst` lacks source directives for `fin`, `vectors`, `finite`, `functions`, `permutations`, `arithmetic`, and `integer`. Add those references and public docstrings together: the current directive omits undocumented declarations and shows only the first signature line. Multi-line dependent signatures and public reexports need deliberate rendering support.

## P1: foundational additions

| Work package | Proposed API and laws | Required edge cases |
| --- | --- | --- |
| Options and decisions | Option elimination, map, bind, default; map identity/composition and bind laws; equality decisions supplied by an element decision procedure | Both constructors; reject unsupported equality; do not assume proof irrelevance |
| Equality decisions | Nat and Int `eq_decide`; structural Option/Sum/List decisions; two-way test/evidence bridges | Unequal constructors, equal values, negative evidence; no classical equality axiom |
| Fin construction | Construct `Fin[n]` from `k` and `LT(k, n)`; round trips with `to_nat`; `Enumeration[Fin[n]]` | `n = 0`, first/last valid index, reject `k = n` |
| Vec interoperability | `tabulate`, `update`, `to_list`, `from_list`; lookup/tabulation, same/other-index update, length and round-trip laws | Empty vector, singleton, unequal indices; use existing `vec_extensional` |
| Lists | `foldr`/`foldl`, safe lookup, zip, take/drop; append/fold laws and length/bound laws | Empty input, unequal zip lengths, out-of-bounds lookup; decide zip/lookup result contracts first |
| Finite construction | Empty/Unit/Bool enumerations, sum/product/option enumerations, cardinality laws; move generic `equality_decide` from `fermat.py` | Completeness and `NoDup`; empty factors; cardinality independent of enumeration |
| Integer laws | Zero/negation laws, add/mul associativity and commutativity, distributivity, comparison reflection/order laws, Nat embedding laws | Zero, both signs, sign changes; retain canonical `Pos(0)` |
| Division contracts | Document total helper behavior at zero; offer checked nonzero-divisor entry points if needed; prove signed division equation, remainder sign and magnitude bound | All sign combinations, exact/nonexact division, zero divisor rejection at checked boundaries |

For division, distinguish the ordinary total library functions from verified `//` and `%`, whose frontend generates nonzero-divisor obligations. Likewise, `arithmetic.sub` truncates at zero while verified Nat subtraction requires a bound. Existing numeric tests cover signed floor-division examples and invalid inputs; general signed theorems are a separate deliverable.

## P2: promote reusable mathematics from examples

Prefer moving checked definitions over creating parallel implementations.

| Source | Promotion candidate | Dependency / scope |
| --- | --- | --- |
| [common.py](../crates/deppy-python/examples/proof_case/common.py) | `Group`, `Subgroup`, recovery/cancellation, `power`, `product`, permutation-independent products | Resolve shared removal evidence first; extract a monoid interface if products need less than a group |
| [lagrange.py](../crates/deppy-python/examples/proof_case/lagrange.py) | `Equivalence`, `Divisible`, rejection/count laws, uniform finite partitions | List/finite foundations; state divisor and zero conventions before adding gcd/modular APIs |
| [fermat.py](../crates/deppy-python/examples/proof_case/fermat.py) | Finite equality decision, power laws, reusable commuting-product laws | Promote finite equality in P1; keep theorem-specific group constructions in examples until independently useful |

Extend `deppy.permutations` with append compatibility, reverse permutation and filter preservation before using it as the common interface for commutative folds/products. Natural-number power, divisibility laws and gcd can follow the foundational arithmetic work. Primality testing and construction of finite fields from modular integers remain distinct projects; the existing Fermat examples do not supply them.

## Delivery order and validation

1. Correct documentation and identify public versus demonstration APIs.
2. Unify removal evidence and migrate finite/proof clients.
3. Add decision/Option helpers and consolidate overlapping Boolean computations.
4. Add Fin construction, enumerations, and Vec/List interoperability.
5. Expand integer/division laws, then promote algebra and finite products.

Each implementation should include accepted and rejected proof clients, axiom-dependency checks, and concrete normalization tests. Add extracted-Python execution tests where values are representable; report erasure budgets or boundary limitations separately. Registry/import smoke coverage should include every supported module, but it does not replace semantic tests. See [verification scope](development.md) for the limits of existing checks.

Universe polymorphism, function extensionality, quotient types, general well-founded recursion, and composite-value support in verified programs require separate language or axiom decisions. They should not be treated as missing Python helper functions or prerequisites for all library expansion.
