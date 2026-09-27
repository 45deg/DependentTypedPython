# Proofs and libraries in Python syntax

`@dependent` bodies are a statically checked pure subset. The frontend does not execute CPython to obtain proofs. Explicit type annotations, motives, and eliminators are available when inference or automatic match lowering is insufficient.

```python
from __future__ import annotations
from deppy import dependent, Nat, Eq, refl, trans

@dependent
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    return trans(refl(n), refl(n))
```

## Modules and imports

The bundled definitions live in `crates/deppy-python/stdlib/deppy/`. They are elaborated as ordinary declarations and rechecked by the kernel. The `deppy` prelude is registered in `registry.rs`; compiler-provided forms are declared with `@builtin` in `_builtins.py` and `tactics.py` and implemented by the frontend. Domain modules include `deppy.nat`, `deppy.equality`, `deppy.fin`, `deppy.vectors`, and the general inductive modules described in [inductive families](inductives.md). Derived equality lemmas such as `trans` and `cong` are Python definitions using `J`, not special frontend operations.

The CLI resolves imports from the input file's parent directory. `from proofs.lemmas import lemma` reads `proofs/lemmas.py` or `proofs/lemmas/__init__.py` beneath that root. Symlinks escaping the root are rejected. Absolute `from module import name`, aliases, and reexports of checked declarations are supported. Relative, wildcard, cyclic, and dynamic imports, site-packages, and use of undecorated Python functions are rejected. The resolver does not run package initialization code. Module names separate same-named declarations. Within each module, declarations must precede their uses.

A source file is limited to 1 MB, the import graph to 8 MB, and import depth to 32; the module count and per-declaration checking steps are also bounded. `check_module_with_resolver` and `compile_module_with_resolver` accept a `SourceResolver`; resolver-free variants use only the standard library, not the current directory. Generated `exports` includes only declarations of the root input module. Define a wrapper in that module to expose an imported function.

## Explicit terms

| Syntax | Meaning |
| --- | --- |
| `Pi[A, lambda x: B]`, `ImplicitPi[A, lambda x: B]` | Explicit or implicit dependent function type |
| `lam(A, lambda x: body)`, `implicit_lam(A, lambda x: body)` | Typed explicit or implicit lambda |
| `ann(value, A)` | Check a term against `A` |
| `f[a, b]` | Supply implicit arguments explicitly |
| `Sigma[A, lambda x: B]`, `Pair(a, b)` | Dependent pair, checked against an expected type |
| `pair(SigmaType, a, b)` | Pair with an explicit type |
| `induct(level, value, motive, *branches)` | General inductive elimination |

An ordinary lambda is checked against an expected dependent function type; use `lam` or `ann` when no expected type is available. `def name() -> A` declares a typed constant, referenced as `name` or `name()`. Arbitrary Python statements and effects are not accepted.

`J(level, A, x, C, base, y, proof)` eliminates `Eq[A,x,y]`, where `C` takes an endpoint and equality proof. `nat_elim`, `vec_elim`, `fin_elim`, and `record_elim` have explicit motives and branches; `fin0_elim` eliminates `Fin[0]`. `level` is a concrete nonnegative universe index. The universes are noncumulative, so a mismatched level is rejected. See [the core reference](reference.md) for typing rules.

## Axioms and opaque theorems

`@axiom` declarations have a typed signature and a sole `...` body. The kernel checks their types but does not consider the axioms proved. They are opaque constants: an assumed `Eq[A,x,y]` does not make `x` and `y` definitionally equal. Unresolved metavariables, holes, or `...` in `@dependent` are never silently promoted to axioms. The CLI reports `[axiom-free]` or `[axioms: ...]`; `CheckedModule.axiom_dependencies` exposes syntactic dependencies, including types, annotations, and referenced declarations.

`@theorem` is `@dependent(opaque=True)`. Its body is checked, then kept opaque for normalization and conversion. It remains callable by its checked type, and its axiom dependencies are retained. Use transparent `@dependent` for definitions intended to compute. Runtime extraction may use the retained checked body even though conversion does not unfold it. No explicit unfold operation is provided.

Axioms have no runtime implementation. Code generation rejects an axiom or proof token needed as runtime data. An axiom-dependent proof can still be extracted when its result is erased. The generator checks all loaded transparent definitions, so even an unused definition requiring an axiom at runtime can cause rejection.

## Proof erasure

After full type checking, `Kernel::erase` removes computations whose result is known to be `Eq` when no runtime consumer needs them. An unused `Eq` let binding may be removed. Proofs passed as runtime arguments, stored in data, or supplied to a data-producing `J` are kept, because later computation may inspect them. A data-producing `J` needing an erased proof is rejected. Public proof results appear as `None`; an internal erased marker remains distinct from a runtime proof token.

Erasure does not change typing, normalization, conversion, or axiom tracking. It does not automatically turn explicit proof arguments into implicit ones or strip proof fields from records, Σ values, or vectors. Transparent definitions may be unfolded to retain a proof required by computation, subject to the checking budget. See `crates/deppy-python/examples/core/proof_erasure.py`.

## Holes, goals, and tactics

`hole("name")` creates a typed goal where an expected type is available. Use `ann(hole("name"), A)` otherwise. `--goals` prints local context and expected type; `--json` returns structured diagnostics and goals. `analyze_module` and `analyze_module_with_resolver` expose the same data. User holes are separate from inference metavariables; even an unused hole leaves the module incomplete. Incomplete declarations are not registered as checked declarations.

`deppy.tactics` declares proof tactics that elaborate to ordinary proof terms checked by the kernel:

| Expression | Effect |
| --- | --- |
| `intro(lambda x: proof)` | Introduce a function hypothesis |
| `exact(proof)` | Check a proof against the goal |
| `apply(lemma, arg, ...)` | Apply a checked lemma, inferring implicit arguments where possible |
| `rewrite(eq, proof)`, `rewrite_in(eq, proof)` | Rewrite a goal or proof type left-to-right |
| `cases(value, {Constructor: branch, ...})` | Exhaustive constructor split at universe 0 |
| `induction(level, value, motive, *branches)` | Nat or general inductive induction |

`rewrite(sym(eq), proof)` reverses direction. If a dependent occurrence cannot be rewritten with a valid type, supply an annotation or an explicit `transport`/`J` motive. Tactics work in named `@verified(proofs={...})` callbacks as well. An unresolved tactic hole is still an unresolved goal.
