# Development and verification

Run commands from the repository root. Cargo dependencies follow `Cargo.lock`; fetch them first with `cargo fetch --locked` if needed. Runtime integration tests require `python3`.

## Rust

```sh
cargo test --workspace --locked --offline
python3 scripts/check_deppy_examples.py
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
```

For a focused Rust check, specify an integration test, for example `cargo test -p deppy-python --locked --offline --test refined`. `check_deppy_examples.py` checks accepted examples, rejected variants, and normalized results through the CLI. Rust integration tests remain for internal API behavior.

## Python

```sh
uv run --no-project --offline --python 3.12 scripts/check_python_syntax.py
uv run --no-project --offline --python 3.14 scripts/check_python_syntax.py
uv run --no-project --offline --python 3.12 scripts/check_python_runtime.py
uv run --no-project --offline --python 3.14 scripts/check_python_runtime.py
python3 scripts/check_fermat.py
```

The syntax check compiles source without executing programs or checking proofs. Runtime differential checks compare fixtures with a test-only reference model; agreement is not a general semantic-preservation proof. Python 3.13 is an accepted parser target, but its runtime behavior has not been checked here.

## Documentation

```sh
uv run --with 'sphinx>=8.2,<9' sphinx-build -W -b html docs docs/_build/html
```

`docs/_ext/deppy_api.py` extracts curated declarations, complete signatures, and docstrings statically without running proof files. Sphinx generates the API reference; Markdown guides remain repository documents. Check their relative links separately.
