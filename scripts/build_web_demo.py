"""Build the client-only DepPy playground assets."""

import json
import shutil
import subprocess
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "web-demo"
EXAMPLES = {
    "basics": ("Basics", OUTPUT / "examples/basics.py"),
    "proof_equality": ("Equality", OUTPUT / "examples/proof_equality.py"),
    "proof_induction": ("Induction", OUTPUT / "examples/proof_induction.py"),
    "proof_vectors": ("Indexed vectors", OUTPUT / "examples/proof_vectors.py"),
    "proof_lists": ("List laws", OUTPUT / "examples/proof_lists.py"),
    "proof_order": ("Order", OUTPUT / "examples/proof_order.py"),
    "algebraic": ("Algebraic: kernel is a subgroup", OUTPUT / "examples/algebraic_kernel.py"),
    "proof_regular_languages": ("Automata: NFA → DFA", OUTPUT / "examples/proof_regular_languages.py"),
    "quicksort": ("Quicksort: sorted output", ROOT / "crates/deppy-python/examples/core/quicksort.py"),
    "fibonacci": ("Fibonacci · recursive = imperative", OUTPUT / "examples/fibonacci.py"),
}


def main() -> None:
    subprocess.run(
        ["cargo", "build", "-p", "deppy-web", "--target", "wasm32-unknown-unknown", "--release", "--locked", "--offline"],
        cwd=ROOT,
        check=True,
    )
    shutil.copyfile(ROOT / "target/wasm32-unknown-unknown/release/deppy_web.wasm", OUTPUT / "checker.wasm")
    examples = {
        key: {"label": label, "source": path.read_text()}
        for key, (label, path) in EXAMPLES.items()
    }
    (OUTPUT / "examples.json").write_text(json.dumps(examples, ensure_ascii=False))
    stdlib = ROOT / "crates/deppy-python/stdlib"
    with zipfile.ZipFile(OUTPUT / "deppy-runtime.zip", "w", zipfile.ZIP_DEFLATED) as archive:
        for path in sorted((stdlib / "deppy").rglob("*.py")):
            archive.write(path, path.relative_to(stdlib))
    print(f"Built static demo in {OUTPUT}")


if __name__ == "__main__":
    main()
