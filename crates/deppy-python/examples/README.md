# DepPy examples

| Directory | Contents |
| --- | --- |
| [`core/`](core/) | Dependent functions, indexed data, records, recursion, and equality proofs |
| [`verified/`](verified/) | Contracts, refined arguments, verified loops, and specification reuse |
| [`proof_case/`](proof_case/) | Cantor's theorem, Lagrange's theorem, and Fermat's theorem |

Run a Python example from the repository root with `cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/core/basics.py`. Examples with local imports keep their dependencies in the same directory. `check.rs` is a Cargo example and stays at this level; run it with `cargo run -p deppy-python --example check --locked --offline`.
