# Running DepPy source with Python

The installable `deppy` package executes the original source files with Python
3.14 or later. It has no Rust dependency and does not invoke the checker. The
package and the Rust frontend use the same standard-library `.py` files in
`crates/deppy-python/stdlib/deppy`; computation and proof-library definitions are
not maintained as separate Python implementations. `_runtime.py` implements the
compiler primitives needed for Python execution.

From the repository root:

```sh
uv venv --python 3.14
uv pip install --python .venv/bin/python -e .
source .venv/bin/activate
python crates/deppy-python/examples/verified/direct.py
# 42
```

For installation without an editable checkout, use `uv pip install .` in an
activated environment. The package includes the standard library and requires
no third-party runtime dependencies.

A source file can contain both checked declarations and an ordinary entry point:

```python
from deppy import Nat, Eq, refl
from deppy.nat import add
from deppy.verified import verified

@verified(
    ensures=lambda n, result: Eq[Nat, result, add(n, n)],
    proof=lambda n, pre: refl(add(n, n)),
)
def twice(n: Nat) -> Nat:
    return n + n

if __name__ == "__main__":
    print(twice(21))
```

Check that file separately when a verification result is needed:

```sh
cargo run -p deppy-python --locked -- path/to/program.py
python path/to/program.py
```

The checker ignores the body of an `if __name__ == "__main__":` block without
`elif` or `else`. Calls, I/O, and other operations there are ordinary Python, not
verified declarations. Merely running a file does not certify it, and editing a
checked file requires checking it again. Direct execution has no connection to a
previous verification result and does not check contracts or input refinements.

## Editor setup

In VS Code, select this repository's `.venv/bin/python` with **Python: Select
Interpreter**. Imports such as `deppy`, `deppy.nat`, and `deppy.verified` then
resolve to the installed package. The package includes generated `.pyi` files
that expose constructors declared inside `@inductive` classes as module-level
imports. They provide import resolution and completion, not DepPy verification
or a translation of dependent types to Python's type system. A Python type
checker can still report diagnostics on DepPy-specific annotations.

After changing standard-library declarations, regenerate the editor surface:

```sh
python scripts/generate_python_stubs.py
python scripts/generate_python_stubs.py --check
```

## Execution behavior and limits

- `@verified` runs the function body without calling its proof or contract
  callbacks. `invariant` and `decreases` do nothing at runtime. Python still
  evaluates argument expressions before passing them to these functions.
- `@dependent` and `@theorem` support explicit generic applications and curried
  calls. Equality-proof results are erased. Other theorem results can contain
  computational data and retain their source computation.
- Natural values use integers, with a small `int` subclass supporting `Z()` and
  `S(k)` patterns. Inductive constructors and records become immutable Python
  objects; `False_()` and `True_()` have the corresponding truth values. Signed
  `Int` values use the library's `Pos` and `Neg` constructors and support Python
  arithmetic; use `int(value)` to obtain a native signed integer.
- Source annotations are not evaluated by the decorators. Source inspection
  supplies record fields and identifies equality-proof results. Records require
  an inspectable source file.
- Python cannot infer all implicit value parameters the DepPy elaborator can
  infer. Supply computationally needed parameters explicitly, e.g. `f[3](x)`.
  Execution that needs erased equality evidence is not supported. `verified_spec`
  returns an erased evidence token; it does not reconstruct contract witnesses.
- Axioms and unresolved holes raise `NotImplementedError` when executed.
  Impossible eliminations raise `RuntimeError`. Recursion is subject to Python's
  recursion limit.

This execution path runs source bodies, whereas `deppy-runtime` extracts checked
core terms. Tests compare selected results with expected values; they do not
establish general equivalence between either Python execution path and the kernel.

## Browser execution

The web playground's **Run** button loads Pyodide 314.0.0 (Python 3.14)
from jsDelivr on demand and runs the editor contents as `main.py`, including
its `if __name__ == "__main__":` block. Select **Fibonacci · recursive = imperative**
for an example that prints `fib(10) = 55`. Examples appear in one flat list. Selecting one updates the URL hash
(e.g. `#quicksort` or `#proof_vectors`), so direct links, reloads, and
browser back/forward navigation select the same example. `#about` opens About.
Every demo has an ordinary entry
point that prints concrete examples; the Quicksort demo includes empty,
reverse-ordered, and duplicate-containing inputs. Equality-proof examples
print `<erased proof>` because equality evidence is erased at runtime. **Check** remains the separate
type/proof checker; completion of a Python run does not mean a proof passed.

`scripts/build_web_demo.py` bundles the same `stdlib/deppy/*.py` sources into
`web-demo/deppy-runtime.zip`; no second runtime implementation is maintained.
Serve the generated assets with `scripts/web_demo.py`. The CDN must be reachable.
Each run starts a fresh Web Worker and Python environment. **Stop** terminates
it, including infinite loops. Standard output and errors appear in Results;
interactive `input()` is unsupported and displayed output is bounded.
