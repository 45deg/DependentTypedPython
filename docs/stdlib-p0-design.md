# P0: canonical types and public library API

This is the implementation contract for P0 of the [standard-library plan](stdlib-plan.md). It fixes ownership, compatibility, and delivery boundaries. Existing behavior remains specified by [math-library.md](math-library.md), [inductives.md](inductives.md), and [verified.md](verified.md).

## Decisions

1. Use the existing standard families as the common vocabulary. Unify removal evidence under `deppy.lists`; retain the separate general-inductive demonstration families.
2. Keep existing checked source imports working through the P0 migration. Distinguish a reexport of a nominal type from a wrapper around a function.
3. Put general Boolean operations in `deppy.bool` and natural Boolean comparisons in a new `deppy.nat_bool`. Keep the compiler's `deppy.verified.*` entry points as real declarations.
4. Preserve the two existing Nat equality algorithms and their reduction behavior in P0. Give them lower-level owners and a proved pointwise equivalence instead of silently replacing one by the other.
5. Curate documentation explicitly. Do not change import visibility, add `__all__` semantics, or broaden the top-level prelude in P0.

## Canonical families

An owner below is the preferred source import path, not necessarily the kernel's internal name. In particular, Nat, Fin, Vec, Eq, Pi and Sigma include compiler-provided forms.

| Family / interface | Preferred owner | Compatibility rule |
| --- | --- | --- |
| `Nat`, `Z`, `S` | `deppy.nat` | Existing `deppy` imports retain the same identity |
| `Fin`, `FZ`, `FS` | `deppy.fin` | Indexed by the canonical Nat |
| `Vec`, `VNil`, `VCons`, `vnil`, `vcons` | `deppy.vectors` | Indexed by the canonical Nat; retain both constructor spellings |
| `Eq`, `refl`, `J` | `deppy.equality` | Preserve the existing builtin identity |
| `Type`, `Pi`, `Sigma`, `Pair` and declaration forms | `deppy` | No new public `core`, `logic`, `records`, `sigma`, or `prelude` modules |
| `Empty`, `Unit`, `Bool`, `Sum`, `Option`, `Decidable`, their constructors, `Not` | `deppy.data` | Operations may reexport the exact family; never redeclare it |
| `List`, `Nil`, `Cons`, `Mem`, `NoDup`, `All`, `Any` | `deppy.lists` | `finite.Has` remains an alias for `lists.Mem` |
| `Removal`, `RemoveHere`, `RemoveThere` | `deppy.lists` | Replace the duplicate finite family by reexports |
| `LE`, `LEZero`, `LESucc`, `LT` | `deppy.nat_order` | Preserve canonical Nat indices and existing evidence representation |
| `Int`, `Pos`, `Neg` | `deppy.integer` | Preserve `Pos(n) = n`, `Neg(n) = -(n + 1)` |
| `Bijection` / `Enumeration` | `deppy.functions` / `deppy.finite` | No changes to record fields or their order |
| `Permutation` and its constructors | `deppy.permutations` | Continue to use `lists.List` |

`deppy.naturals.Nat` and `deppy.indexed.IVec` / `IFin` remain supported **demonstration APIs**, at their current paths, with their current nominal identities. They exercise general inductive declarations and indexed patterns. They must not be used as indices for new canonical Fin/Vec APIs. Documentation must show aliases such as `Nat as DemoNat` when both natural families appear together. P0 adds no implicit conversion, rename, or removal; explicit conversions can be a separate extension if a client needs them.

## Removal migration

Keep these signatures and constructor field orders from `lists.py`:

```python
@inductive
class Removal[A: Type, x: A]:
    source: Index[List[A]]
    rest: Index[List[A]]

    @constructor
    def RemoveHere(tail: List[A]) -> Removal[A, x, Cons(x, tail), tail]: ...

    @constructor
    def RemoveThere(
        head: A, ys: List[A], zs: List[A], step: Removal[A, x, ys, zs]
    ) -> Removal[A, x, Cons(head, ys), Cons(head, zs)]: ...

@theorem(decreases="xs")
def find_removal[A: Type](
    x: A, xs: List[A], member: Mem(x, xs)
) -> Sigma[List[A], lambda rest: Removal[A, x, xs, rest]]: ...
```

The fragment describes signatures, not executable replacement bodies. `find_removal` stays opaque: it returns a witness in a Sigma but is currently a theorem, so P0 must not promise reduction of its `.fst` to a concrete remainder. A separately named executable removal search belongs to a later change.

Delete the duplicate family, constructors and `find_removal` definition from `finite.py`, replacing them with explicit imports from `deppy.lists`. Both import paths must then resolve to the **same binding**, including constructor metadata and family identity. A wrapper class or conversion function would not meet this requirement.

`lists.removal_mem` and `lists.removal_length` remain in place. Keep these finite laws at their existing paths, now consuming the shared family: `removal_present`, `removal_include`, `removal_keep`, `removal_nodup`, `removal_absent`, and `removal_count`. `removal_present` may delegate to `lists.removal_mem` while retaining its theorem declaration. Moving all those laws between modules is unnecessary for this migration.

Preserve `finite.Either`, `Decision`, `Unit_`, `Has`, `either_elim`, and `map_injective_has`. Their preferred equivalents are `data.Sum`, `data.Decidable`, `data.MkUnit`, `lists.Mem`, `data.sum_elim`, and `lists.map_mem_reflect`. Preserve existing argument order in any wrapper. Update `examples/proof_case/common.py` to import the canonical removal family and search from `lists`; its clients must continue to work through its reexports. Keep a separate test client using the old `finite` import path.

This preserves checked **source** compatibility, not the old `deppy.finite.Removal` nominal tag in previously extracted values. Recheck sources and regenerate extracted artifacts together. Do not introduce a second runtime family to preserve that tag, and do not claim compatibility for serialized values or old Python wrappers mixed with regenerated ones.

## Computation and dependency direction

The current `arithmetic` module imports `verified`, while the lowerer emits hard-coded names such as `deppy.verified.nat_eq`, `bool_not`, `select`, and `select_post_eq`. The auto prover also names several verified lemmas directly. Reexporting those functions alone would change checked binding origins without supplying the declarations required by those emitted names.

### Boolean ownership

Move the following general helpers from `verified` to `bool`, preserving signatures and decorators:

| Kind | Names in `deppy.bool` after migration |
| --- | --- |
| Branch computation and laws | `select`, `select_post`, `select_post_eq` |
| Constructive decision bridge | `decision_bool`, `decision_true`, `decision_true_intro` |
| Boolean comparison | `bool_eq` |
| Compatibility computation | `bool_not`, retaining the old selection body if it is not convertible to `negate` |
| Contradiction and branch evidence | `false_ne_true`, `false_true_elim`, `true_false_elim`, `not_false`, `and_left`, `and_right` |
| Supporting discriminator | `false_type` (implementation helper, preserved as a compatibility import) |

Existing `bool.negate`, algebraic operations, `eq_decide`, `is_true`, and their laws remain the preferred API. Move the old `bool_not` computation to `bool.bool_not`; `verified.bool_not` becomes a transparent wrapper over it. General helpers such as `not_false` use this lower-level definition, never an import back from `verified`. Implement `bool.bool_not` as a transparent call to `negate` only when the conversion checks below pass. The old body uses `select`; compare neutral as well as closed inputs before changing it. If the neutral terms are not definitionally equal, retain that body and prove an opaque, axiom-free `bool_not_negate(flag: Bool) -> Eq[Bool, bool_not(flag), negate(flag)]` bridge; do not weaken the client's proof obligation or change the kernel.

Preserve `select(flag, no, yes)` argument order. Preserve `and_left` / `and_right` statements in terms of `select`; a change to the statement using `conjunction` is not required. `decision_bool` consumes `Decidable[P]`; `decision_true` eliminates a true test to `P`, and `decision_true_intro` takes a witness of `P`. This does not assert equality of decision proofs. Keep `is_true(b)` and `Eq[Bool, b, True_()]` as distinct proposition presentations with the existing intro/elim bridges.

### Natural comparison ownership

Register `deppy.nat_bool` as an ordinary checked source module. It imports only `_builtins`, `equality`, `data`, `bool`, `nat`, and `nat_order`. It does not import `arithmetic`, `integer`, `verified`, or the `deppy` prelude.

| Current name | Canonical destination | Reduction contract |
| --- | --- | --- |
| `verified.nat_le`, `nat_lt` | `nat_bool.nat_le`, `nat_lt` | Keep the existing `decision_bool(le_decide/lt_decide(...))` bodies |
| `verified.nat_eq` | `nat_bool.nat_eq` | Keep comparison in both directions and the existing selection order |
| `verified.nat_lt_true`, `nat_le_true`, `nat_eq_true`, `nat_le_refl_true` | Same names in `nat_bool` | Keep statements and theorem opacity |
| `verified.nat_lt_false_zero`, `lt_le_bound`, `pred_lt_true`, `nat_lt_not_false` | Same names in `nat_bool` | Keep their evidence arguments and statements |
| `arithmetic.equal`, `equal_true`, `equal_refl`, `equal_false` | Same names in `nat_bool` | Preserve structural recursion and existing decorators |
| `arithmetic.is_zero`, `equal_step`, `zero_equal`, `step_equal` | Same names in `nat_bool` | Supporting definitions move with the structural equality implementation |

For new ordinary Nat Boolean equality clients, prefer `nat_bool.equal`. For compatibility with verified guards, use `nat_bool.nat_eq` and its reflection theorem. `eq_decide` means a constructive decision returning `Decidable[Eq[...]]`; do not use that name for either Boolean function. A new Nat `eq_decide` is P1 work.

Add an opaque, axiom-free pointwise law in `nat_bool`:

```python
@theorem
def equal_nat_eq(n: Nat, m: Nat) -> Eq[Bool, equal(n, m), nat_eq(n, m)]: ...
```

Prove the law by checked induction/Boolean cases and existing reflection facts. No function extensionality is needed. Equal outputs on literals do not establish definitional equality on variables; P0 retains both algorithms even after this theorem exists. Replacing the verified comparison algorithm is a separate optimization with its own compatibility and performance checks.

### Compatibility declarations and imports

Keep real declarations with the original signatures at every existing `verified` function path listed above. Computational wrappers use `@dependent`; theorem wrappers retain `@theorem` and call the new owner. Rename imports locally to avoid shadowing wrappers. Keep compiler-emitted fully qualified names unchanged in this work package, and verify every such name still exists in the checked environment, not just in its alias table. The same rule applies to automatically selected proof helpers.

Keep the old `arithmetic` equality names as explicit compatibility reexports of `nat_bool`. Their implementation bodies and opacity do not change. Current source clients resolve aliases to the new owner; internal qualified origins may change. No binary, diagnostic-text, or serialized checked-environment compatibility is promised.

Switch `arithmetic` to import general helpers directly from `bool` and `nat_bool`. Switch `integer`'s general helper imports likewise; its `verified` and `Refined` syntax imports may remain because `to_nat` has a verified contract. Keep `verified_loop`'s compiler support imports intact initially. The dependency requirement is:

```text
bool       -> data, equality
nat_bool   -> bool, nat_order, nat, data, equality
arithmetic -> nat_bool, bool, nat_order, nat, data, equality
verified   -> nat_bool, bool, nat_order, nat, data, equality
integer    -> arithmetic, nat_bool, bool, verified
```

Arrows mean imports; common builtin edges are omitted. The remaining `integer -> verified` edge supports its checked conversion contract. `verified` must not import `integer` or `arithmetic`; the lowerer's conditional loading of numeric support remains separate from source imports. `data`, `nat`, and `nat_order` must not acquire imports of `bool` or `nat_bool`. Lists, finite carriers and permutations retain their existing acyclic direction.

## Supported exports and documentation

Use four documentation categories:

| Category | Meaning |
| --- | --- |
| Canonical | Preferred imports for new clients: the family table, owning-module operations/laws, and the new general helpers above |
| Compatibility | Retained paths/aliases, including the finite aliases, verified wrappers and arithmetic equality reexports |
| Demonstration | `naturals` and `indexed`, explicitly using a different Nat family |
| Implementation | Motives, recursion steps, and proof plumbing; importable today, but not recommended building blocks |

All current exports remain resolvable during P0, including incidental imported names. Before moving definitions, capture the affected modules' checked export names and retain explicit imports for names that would otherwise disappear with an unused-import cleanup. Compare that inventory after each slice; preserve nominal identity except for the deliberate finite removal migration. Classification alone does not remove names, make them private, or make an existing client invalid. A later visibility change needs a separate proposal and migration. Do not infer categories from a leading underscore, a suffix such as `_head`, or the existence of a docstring: some helpers are used by checked proof clients.

For the changed areas, canonical public names are the families and operations/laws explicitly named above, plus the existing Boolean algebra API. Compatibility names are the old paths in the migration tables, `bool.bool_not` and its bridge if needed, and the aliases in the removal section. In `bool`, `false_type` is an implementation helper. In `nat_bool`, `is_zero`, `equal_step`, `zero_equal`, and `step_equal` are implementation helpers; `equal`, its three laws, all moved order/guard laws, and `equal_nat_eq` are canonical. In `finite`, `finite_all_from_decision`, `finite_any_from_decision`, `tail_forward`, `tail_backward`, `SameCountAt`, `same_count_nil`, and `same_count_step` are implementation helpers whose imports remain available. Existing operations/laws outside these areas keep their current paths; P0 does not rename them.

The top-level `deppy` prelude stays at the explicit import list in `registry.rs`. New comparison, list, finite and integer APIs require imports from their owning module. `deppy._builtins` is compiler infrastructure, not the recommended user-facing namespace. `deppy.tactics` remains a public module with compiler-provided declarations.

Implement curated reference generation by extending the existing `deppy-api` directive, not by executing source modules:

- Add an explicit `:members:` list to select canonical local declarations. A selected name without a docstring or declaration is a build error, not a silent omission. Keep the current default for example directives until they are migrated.
- Render complete multiline signatures, explicit type parameters, and record/index fields and constructor signatures. Builtin declarations need their source annotations rendered without attempting Python execution.
- Give each canonical entry one qualified anchor. Document compatibility reexports in a separate alias table linking to that anchor, so imported names do not require duplicate declaration bodies or automatic recursive import resolution.
- Cover `fin`, `vectors`, `finite`, `functions`, `permutations`, `arithmetic`, `integer`, and the new `nat_bool` alongside the existing sections. Document `naturals` / `indexed` separately as demonstrations. Update `math-library.md` when the source moves actually land.
- Check the selected names and aliases against the checked import interface, including constructor identity. Static AST extraction alone cannot establish that an import works.

This gives the documentation an explicit supported surface without making `__all__`, decorators, docstrings, or Sphinx options part of the checked language.

## Implementation slices and acceptance gates

Each slice must leave checked sources usable. Add tests to the existing suites rather than introducing another checker.

| Slice | Source changes | Required evidence |
| --- | --- | --- |
| 1. Shared removal | `lists`, `finite`, proof-case imports | Both import paths share family and constructor bindings; a lists proof feeds finite removal/count laws and a finite-imported constructor feeds lists laws; invalid source/rest indices are rejected; Lagrange and both Fermat developments still check |
| 2. Boolean layer | `bool`, verified wrappers | Literal truth tables and neutral-input conversion fixtures; existing Boolean laws, branch VCs and contradiction helpers still check; emitted verified names remain actual declarations |
| 3. Nat comparison layer | New `nat_bool`, registry, verified/arithmetic wrappers and imports, integer imports | Both equality algorithms preserve their existing reductions; `equal_nat_eq` checks without axioms; false equality/order evidence is rejected; direct imports work without cycles; numeric and refinement clients still check |
| 4. Public reference | Directive, API reference, overview | Complete signatures/constructors, missing-member failures, working alias links, all canonical imports checked, warning-free Sphinx build |

For slice 1, use constructor-built removal evidence to test length and count laws; do not try to normalize the opaque search witness. Include two occurrences of the same element so that removal means **one occurrence**, not filtering all equal elements. Keep source-level old-import fixtures even after the examples use canonical imports.

For slices 2–3, preserve reduction on open terms as well as small closed values: wrap the old body in a test fixture and attempt `refl` against the new body with arbitrary inputs. Cover Boolean variables, zero/successor Nat arguments, equal and unequal pairs, and original theorem statements. A failed conversion test means the wrapper switch is incompatible; retain the legacy body and expose a propositional bridge instead. Do not substitute an equality axiom. Computational definitions stay transparent; theorem opacity stays unchanged.

Use `libraries`, `data`, `bool`, `nat_order`, and `lagrange` integration suites for the relevant slices. Use `verified`, `verified_expressions`, `verified_control`, `verified_numeric`, `verified_loop`, `verified_spec`, and the refinement suites for comparison/bridge changes, then the workspace checks in [development.md](development.md). Run `scripts/check_fermat.py` for its accepted/rejected proof clients; separately check `examples/proof_case/fermat2.py`, which that script does not cover. Record any existing proof budgets rather than increasing them to conceal a regression.

All new general laws must have empty axiom dependencies. Existing clients must not gain axiom dependencies. Keep the general-inductive tests and include rejection of a demonstration Nat where canonical Nat is required. Report checking/normalization, extracted-Python execution, and documentation rendering separately; passing one is not evidence for the others.

P0 is implemented only when all four slices pass these gates. Option operations, new constructive equality procedures, Fin/Vec interoperability, integer algebra, and promoted group theory remain P1/P2 work.
