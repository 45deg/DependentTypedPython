# DepPy

DepPy is a dependently typed language with Python syntax. `@dependent` defines total functions and proofs; `@verified` checks an imperative subset by generating verification conditions (VCs). Proof terms are checked independently of source execution. Source files and annotations are read statically; DepPy does not run them to obtain proofs.

DepPy is experimental and under construction. It accepts a documented subset of Python syntax and does not establish a general equivalence between Python source, checked terms, and generated Python code. See [Current limitations](#current-limitations) before relying on generated programs.

The kernel checks dependent functions, equality proofs, indexed inductive families, and structural recursion. The verified frontend supports contracts, local assignment, branches, loops, and a limited proof search. Its VCs become dependent core propositions checked by the same kernel. Generated programs are separate from proof validity. See the [language specification](docs/reference.md), [proof guide](docs/proofs.md), and [verified specification](docs/verified.md) for the accepted subset and limits.

## Example

From [proofs.py](crates/deppy-python/examples/core/proofs.py), a proof by induction that adding zero on the right leaves a natural number unchanged:

```python
from deppy import dependent, Nat, Eq, Z, S, refl, cong

@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, n + 0, n]:
    match n:
        case Z():
            return refl(Z())
        case S(k):
            return cong(S, zero_right(k))
```

```sh
cargo run -p deppy-python --locked --offline -- eval crates/deppy-python/examples/core/proofs.py zero_right 0
# refl(0)
```

## Current limitations

The checker covers the [specified language subset](docs/reference.md), not arbitrary Python. Unsupported syntax and proof obligations are rejected. Generated Python has been compared with a test reference model on selected examples, but general preservation of source behavior and proof erasure has not been established. Some proof exports remain unsupported because their computations require erased arguments. Deep recursion has no stack or memory guarantee. See the [verification scope](docs/development.md) and [roadmap](docs/roadmap.md) for the evidence and remaining work.

## Examples

Examples are grouped by purpose: [core](crates/deppy-python/examples/core/) covers dependent functions, data types, and proofs; [verified](crates/deppy-python/examples/verified/) covers contracts, refined values, and loops; [proof_case](crates/deppy-python/examples/proof_case/) contains larger mathematical proofs.

The proof cases include [Lagrange's theorem](crates/deppy-python/examples/proof_case/lagrange.py) and [Fermat's theorem via Lagrange](crates/deppy-python/examples/proof_case/fermat.py). They share finite enumeration and group definitions in [common.py](crates/deppy-python/examples/proof_case/common.py). The Fermat example assumes a finite field's nonzero multiplicative group and its enumeration; it does not construct a field from primality or modular arithmetic.

The [Cantor example](crates/deppy-python/examples/proof_case/cantor.py) proves by diagonalization that no map from `A` to Boolean-valued functions on `A` is surjective. It uses no axioms or function extensionality.

The [documentation index](docs/README.md) links the specifications, verification scope, and remaining work. A concise [Japanese guide](docs/ja/README.md) is also available.
