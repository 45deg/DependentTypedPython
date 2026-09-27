# DepPy

DepPy is a dependently typed language with Python syntax. `@dependent` defines total functions and proofs; `@verified` checks an imperative subset by generating verification conditions (VCs). A Rust kernel checks the resulting proof terms. Source files and annotations are read statically; DepPy does not run them to obtain proofs.

DepPy is experimental. It accepts a documented subset of Python syntax and does not establish a general equivalence between Python source, checked terms, and generated Python code. See [Current limitations](#current-limitations) before relying on generated programs.

The repository contains five crates:

| Crate | Responsibility |
| --- | --- |
| `deppy-core` | Explicit terms, kernel, normalization by evaluation, axiom tracking, and checked projection to runtime IR |
| `deppy-elab` | Named AST, bidirectional elaboration, metavariables, definitions, and structural recursion |
| `deppy-python` | Ruff-based parser, static modules, `@dependent` and `@verified` lowering, and VC generation |
| `deppy-runtime` | Optional Python generator, runtime shim, public boundary wrappers, and CLI |
| `deppy-web` | WebAssembly checker used by the browser demo |

The kernel checks dependent functions, equality proofs, indexed inductive families, and structural recursion. The verified frontend supports contracts, local assignment, branches, loops, and a limited proof search. Its VCs become dependent core propositions checked by the same kernel. The runtime backend is separate from proof validity. See the [language specification](docs/reference.md), [proof guide](docs/proofs.md), and [verified specification](docs/verified.md) for the accepted subset and limits.

## Try it

Install a Rust toolchain with Cargo and Python 3.14, then run these commands from the repository root. Cargo uses `Cargo.lock`; fetch dependencies once with `cargo fetch --locked` if they are not cached. The `--offline` commands below require that fetch to have succeeded.

```sh
cargo test --workspace --locked --offline
python3 scripts/check_deppy_examples.py
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/core/basics.py
cargo run -p deppy-python --locked --offline -- eval crates/deppy-python/examples/core/basics.py twice 0
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified/verified_annotations.py
cargo run -p deppy-python --locked --offline -- --goals path/to/proof.py
cargo run -p deppy-runtime --locked --offline -- crates/deppy-python/examples/core/proofs.py
```

`--elaboration-steps N` sets a positive, per-declaration checking budget; the default is 1,000,000. Raising it changes neither typing rules nor axiom handling.
`eval FILE.py NAME [NAT ...]` checks the module, applies the named checked declaration to natural-number arguments, and prints its kernel-normalized result. For example, `twice 0` prints `2` and `reflexive 0` prints `refl(0)`. This evaluates DepPy terms without executing the source as Python.

### Browser demo

Install the Rust WebAssembly target, then build the checker and static assets from the repository root:

```sh
rustup target add wasm32-unknown-unknown
python3 scripts/build_web_demo.py
python3 scripts/web_demo.py
```

Open <http://127.0.0.1:8000/>. The browser runs the DepPy checker in WebAssembly; no verification API or server-side Python execution is used. The Python server only serves static files and binds to localhost. The same `web-demo/` files can be served by a static host. The demo offers editable examples, including six commented proof parts (ending with a group homomorphism kernel theorem) and a verified Fibonacci loop equal to its recursive specification. It shows diagnostics and open goals, with a 64 KiB source limit. Submitted Python source is never executed or sent to a server. Use `--port N` to choose another port.

To publish at `https://45deg.github.io/deppy-web/`, copy the built contents of `web-demo/` (including `checker.wasm`, `examples.json`, and `github-invertocat-black.svg`) into `deppy-web/` in the `45deg.github.io` site's published source. The demo uses relative asset URLs and needs no path rewrite. GitHub Pages for the separate `45deg/DepPy` repository would instead use `/DepPy/` by default; putting this repository at `origin` does not publish the requested `/deppy-web/` path. The GitHub header link points to the planned `45deg/DepPy` repository. Its icon is the unmodified black Invertocat SVG from [GitHub's official Brand Toolkit](https://brand.github.com/foundations/logo).

The editor loads CodeMirror 6 and Python language support from pinned JSPM CDN URLs. If the CDN is unavailable, the plain textarea remains usable.

## Current limitations

The checker covers the [specified language subset](docs/reference.md), not arbitrary Python. Unsupported syntax and proof obligations are rejected. Generated Python has been compared with a test reference model on selected examples, but general preservation of source behavior and proof erasure has not been established. Generated execution of the verified numeric examples remains unverified because proof erasure exceeds the default checking budget. Deep recursion has no stack or memory guarantee. Executing source files as Python requires 3.14 for deferred annotations. See the [development checks](docs/development.md) and [roadmap](docs/roadmap.md) for the evidence and remaining work.

## Examples

Python examples are grouped by purpose: [core](crates/deppy-python/examples/core/) covers dependent functions, data types, and proofs; [verified](crates/deppy-python/examples/verified/) covers contracts, refined values, and loops; [proof_case](crates/deppy-python/examples/proof_case/) contains larger mathematical proofs. The Cargo example `check.rs` stays at the `examples/` root.

The proof cases include [Lagrange's theorem](crates/deppy-python/examples/proof_case/lagrange.py) and [Fermat's theorem via Lagrange](crates/deppy-python/examples/proof_case/fermat.py). They share finite enumeration and group definitions in [common.py](crates/deppy-python/examples/proof_case/common.py). The Fermat example assumes a finite field's nonzero multiplicative group and its enumeration; it does not construct a field from primality or modular arithmetic.

The [Cantor example](crates/deppy-python/examples/proof_case/cantor.py) proves by diagonalization that no map from `A` to Boolean-valued functions on `A` is surjective. It uses no axioms or function extensionality.

```sh
cargo run -p deppy-python --locked --offline -- --elaboration-steps 100000000 crates/deppy-python/examples/proof_case/fermat.py
python3 scripts/check_fermat.py
```

The [documentation index](docs/README.md) links the specifications, development checks, and remaining work. A concise [Japanese guide](docs/ja/README.md) is also available.
