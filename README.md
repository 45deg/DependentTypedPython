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
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/core/basics.py
cargo run -p deppy-python --locked --offline -- eval crates/deppy-python/examples/core/basics.py twice 0
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified/verified_annotations.py
cargo run -p deppy-python --locked --offline -- --goals path/to/proof.py
cargo run -p deppy-runtime --locked --offline -- crates/deppy-python/examples/core/proofs.py
```

`--elaboration-steps N` sets a positive, per-declaration checking budget; the default is 1,000,000. Raising it changes neither typing rules nor axiom handling.
`eval FILE.py NAME [NAT ...]` checks the module, applies the named checked declaration to natural-number arguments, and prints its kernel-normalized result. For example, `twice 0` prints `2` and `reflexive 0` prints `refl(0)`. This evaluates DepPy terms without executing the source as Python.

### Browser demo

Build the WebAssembly checker and static assets from the repository root:

```sh
python3 scripts/build_web_demo.py
python3 scripts/web_demo.py
```

Open <http://127.0.0.1:8000/>. The browser runs the DepPy checker in WebAssembly; no verification API or server-side Python execution is used. The Python server only serves static files and binds to localhost. The same `web-demo/` files can be served by a static host. The demo offers editable examples and shows diagnostics and open goals, with a 64 KiB source limit. Submitted Python source is never executed or sent to a server. Use `--port N` to choose another port.

The editor loads CodeMirror 6 and Python language support from pinned JSPM CDN URLs. If the CDN is unavailable, the plain textarea remains usable.

## Examples

Python examples are grouped by purpose: [core](crates/deppy-python/examples/core/) covers dependent functions, data types, and proofs; [verified](crates/deppy-python/examples/verified/) covers contracts, refined values, and loops; [proof_case](crates/deppy-python/examples/proof_case/) contains larger mathematical proofs. The Cargo example `check.rs` stays at the `examples/` root.

The proof cases include [Lagrange's theorem](crates/deppy-python/examples/proof_case/lagrange.py) and [Fermat's theorem via Lagrange](crates/deppy-python/examples/proof_case/fermat.py). They share finite enumeration and group definitions in [common.py](crates/deppy-python/examples/proof_case/common.py). The Fermat example assumes a finite field's nonzero multiplicative group and its enumeration; it does not construct a field from primality or modular arithmetic.

The [Cantor example](crates/deppy-python/examples/proof_case/cantor.py) proves by diagonalization that no map from `A` to Boolean-valued functions on `A` is surjective. It uses no axioms or function extensionality.

```sh
cargo run -p deppy-python --locked --offline -- --elaboration-steps 100000000 crates/deppy-python/examples/proof_case/fermat.py
python3 scripts/check_fermat.py
```

The [documentation index](docs/README.md) links the specifications, development checks, and remaining work. A concise [Japanese guide](docs/ja/README.md) is also available.
