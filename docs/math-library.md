# Mathematical library

Mathematical definitions and proofs are checked Python declarations. The library does not add theorem-specific kernel primitives. A built-in module still needs an entry in the frontend's module registry for static imports.

## Available modules

| Module | Public scope |
| --- | --- |
| `deppy.equality` | `sym`, `trans`, `cong`, `cong2`, `transport`, and transport laws |
| `deppy.data`, `deppy.logic` | Sum elimination, negation, product/sum/implication decisions |
| `deppy.nat` | Addition, multiplication, associativity, commutativity, distributivity, subtraction relations, quotient/remainder equations and bounds |
| `deppy.nat_order` | `LE`, `LT`, reflexivity, successor and transitivity lemmas, decisions, total order, and cancellation by a positive factor |
| `deppy.lists` | `length`, membership, `NoDup`, `All`, `Any`, `filter`, element removal, and standard list theorems |
| `deppy.fin`, `deppy.vectors` | Fin-to-Nat bounds, map, append, reverse, and lookup lemmas |
| `deppy.finite` | `Enumeration`, order-independent count, and count preservation under bijection |

The [Lagrange](../crates/deppy-python/examples/proof_case/lagrange.py) and [Fermat](../crates/deppy-python/examples/proof_case/fermat.py) examples define more finite-set, group, and product machinery in example sources. The [direct Fermat proof](../crates/deppy-python/examples/proof_case/fermat2.py) uses product permutation and cancellation instead of Lagrange. These examples assume a supplied finite enumeration and group/field structure; they do not define a primality test or construct finite fields from modular integers.

## Library rules

Use one shared family for a foundational type before promoting example code into the standard library. `deppy.nat.Nat`, `deppy.data.Bool`, `deppy.lists.List`, and the checked indexed types should remain the common vocabulary. Conversion between example-local and standard types is a migration task, not a kernel rule.

Keep executable definitions transparent when computation is part of the API. Use `@theorem` for checked opaque laws whose bodies should not unfold during conversion. Do not assume equality of proofs, function extensionality, choice, or quotient types implicitly. Any additional principle must be declared as an axiom and tracked.

Finite enumeration, permutations, finite products, divisibility, and group theory are candidates for standard modules. A public API should hide implementation-specific induction helpers behind curated reexports; a leading underscore alone does not guarantee privacy in the current lowerer. Prefer Type₀ carriers until universe polymorphism exists.

For proposed library extensions, see the [roadmap](roadmap.md). A promoted API needs general checked statements, no theorem-specific primitive, positive and negative tests, and executable examples where runtime values are representable.
