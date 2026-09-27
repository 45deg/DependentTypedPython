# Mathematical library

Mathematical definitions and proofs are checked Python declarations. The library does not add theorem-specific kernel primitives. A built-in module still needs an entry in the frontend's module registry for static imports.

## Available modules

| Module | Public scope |
| --- | --- |
| `deppy.equality` | `sym`, `trans`, `cong`, `cong2`, `transport`, and transport laws |
| `deppy.data` | Sum elimination, negation, product/sum/implication decisions |
| `deppy.bool` | `negate`, `conjunction`, `disjunction`, `xor`, constructive equality decisions, branch selection, Boolean algebra laws, and truth evidence |
| `deppy.nat` | Addition, multiplication, associativity, commutativity, distributivity, and cancellation |
| `deppy.nat_bool` | Natural Boolean order and equality comparisons, their reflection laws, and the pointwise equivalence of structural and order based equality |
| `deppy.arithmetic` | Truncated subtraction, subtraction relations, quotient/remainder equations and bounds; the former equality names reexport `deppy.nat_bool` |
| `deppy.integer` | Canonical signed integers, arithmetic, comparisons, floor division, and checked conversion to Nat |
| `deppy.nat_order` | `LE`, `LT`, reflexivity, successor and transitivity lemmas, decisions, total order, and cancellation by a positive factor |
| `deppy.lists` | `length`, membership, `NoDup`, `All`, `Any`, `filter`, canonical one occurrence removal evidence, and standard list theorems |
| `deppy.fin`, `deppy.vectors` | Fin-to-Nat bounds, map, append, reverse, and lookup lemmas |
| `deppy.finite` | `Enumeration`, order-independent count, count preservation under bijection, and removal/count laws over `deppy.lists.Removal` |
| `deppy.functions` | Bijections, identity, inverse, composition, injectivity, and surjectivity |
| `deppy.permutations` | List permutations and preservation of length, membership, `NoDup`, and map |
| `deppy.verified`, `deppy.verified_loop` | Compatibility declarations used by generated verified proofs, checked loop interpreters, and range obligations |
| `deppy.indexed` | General-inductive IVec/IFin demonstrations indexed by the canonical Nat |

The [Lagrange](../crates/deppy-python/examples/proof_case/lagrange.py) and [Fermat](../crates/deppy-python/examples/proof_case/fermat.py) examples define more finite-set, group, and product machinery in example sources. These examples assume a supplied finite enumeration and group/field structure; they do not define a primality test or construct finite fields from modular integers.

## Library rules

Use one shared family for a foundational type before promoting example code into the standard library. `deppy.nat.Nat`, `deppy.data.Bool`, `deppy.lists.List`, and the checked indexed types should remain the common vocabulary.

Keep executable definitions transparent when computation is part of the API. Use `@theorem` for checked opaque laws whose bodies should not unfold during conversion. Do not assume equality of proofs, function extensionality, choice, or quotient types implicitly. Any additional principle must be declared as an axiom and tracked.

Finite enumeration and permutations already have standard modules. Standard enumerations, broader permutation laws, finite products, divisibility, and group theory remain extension candidates. The [generated reference](math-api.rst) curates supported declarations and lists compatibility paths without changing import visibility. A leading underscore alone does not guarantee privacy in the current lowerer. Prefer Type₀ carriers until universe polymorphism exists.

For proposed library extensions, see the [standard-library plan](stdlib-plan.md) and [roadmap](roadmap.md). A promoted API needs general checked statements, no theorem-specific primitive, positive and negative tests, and executable examples where runtime values are representable.
