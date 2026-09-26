# DepPy

DepPy is a dependently typed language with Python syntax. `@dependent` defines total functions and proofs; `@verified` checks an imperative subset by generating verification conditions (VCs). A Rust kernel checks the resulting proof terms. Source files and annotations are read statically; DepPy does not run them to obtain proofs.

The repository contains four crates:

| Crate | Responsibility |
| --- | --- |
| `deppy-core` | Explicit terms, kernel, normalization by evaluation, axiom tracking, and checked projection to runtime IR |
| `deppy-elab` | Named AST, bidirectional elaboration, metavariables, definitions, and structural recursion |
| `deppy-python` | Ruff-based parser, static modules, `@dependent` and `@verified` lowering, and VC generation |
| `deppy-runtime` | Optional Python generator, runtime shim, public boundary wrappers, and CLI |

The kernel checks dependent functions, equality proofs, indexed inductive families, and structural recursion. The verified frontend supports contracts, local assignment, branches, loops, and a limited proof search. Its VCs become dependent core propositions checked by the same kernel. The runtime backend is separate from proof validity. See the [language specification](docs/reference.md), [proof guide](docs/proofs.md), and [verified specification](docs/verified.md) for the accepted subset and limits.

## Try it

Cargo uses `Cargo.lock`. Fetch dependencies once with `cargo fetch --locked` if they are not cached.

```sh
cargo test --workspace --locked --offline
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/basics.py
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified_annotations.py
cargo run -p deppy-python --locked --offline -- --goals path/to/proof.py
cargo run -p deppy-runtime --locked --offline -- crates/deppy-python/examples/proofs.py
```

`--elaboration-steps N` sets a positive, per-declaration checking budget; the default is 1,000,000. Raising it changes neither typing rules nor axiom handling.

The [proof examples](crates/deppy-python/examples/proof_case/) include [Lagrange's theorem](crates/deppy-python/examples/proof_case/lagrange.py), [Fermat's theorem via Lagrange](crates/deppy-python/examples/proof_case/fermat.py), and a [direct Fermat proof](crates/deppy-python/examples/proof_case/fermat2.py). They share finite enumeration and group definitions in [common.py](crates/deppy-python/examples/proof_case/common.py). The Fermat examples assume a finite field's nonzero multiplicative group and its enumeration; they do not construct a field from primality or modular arithmetic.

```sh
cargo run -p deppy-python --locked --offline -- --elaboration-steps 100000000 crates/deppy-python/examples/proof_case/fermat.py
python3 scripts/check_fermat.py
```

The [documentation index](docs/README.md) links the specifications, development checks, and remaining work. A concise [Japanese guide](docs/ja/README.md) is also available.
