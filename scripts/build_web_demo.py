"""Build the client-only DepPy playground assets."""

import json
import shutil
import subprocess
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "web-demo"
EXAMPLES = {
    "basics": ("Basics", "Start", OUTPUT / "examples/basics.py"),
    "proof_equality": ("Part 1 · Equality", "Proofs", OUTPUT / "examples/proof_equality.py"),
    "proof_induction": ("Part 2 · Induction", "Proofs", OUTPUT / "examples/proof_induction.py"),
    "proof_vectors": ("Part 3 · Indexed vectors", "Proofs", OUTPUT / "examples/proof_vectors.py"),
    "proof_lists": ("Part 4 · List laws", "Proofs", OUTPUT / "examples/proof_lists.py"),
    "proof_order": ("Part 5 · Order", "Proofs", OUTPUT / "examples/proof_order.py"),
    "algebraic": ("Part 6 · Algebraic: kernel is a subgroup", "Proofs", OUTPUT / "examples/algebraic_kernel.py"),
    "fibonacci": ("Fibonacci · recursive = imperative", "Verified Programs", OUTPUT / "examples/fibonacci.py"),
}


def main() -> None:
    subprocess.run(
        ["cargo", "build", "-p", "deppy-web", "--target", "wasm32-unknown-unknown", "--release", "--locked", "--offline"],
        cwd=ROOT,
        check=True,
    )
    shutil.copyfile(ROOT / "target/wasm32-unknown-unknown/release/deppy_web.wasm", OUTPUT / "checker.wasm")
    examples = {
        key: {"label": label, "group": group, "source": path.read_text()}
        for key, (label, group, path) in EXAMPLES.items()
    }
    (OUTPUT / "examples.json").write_text(json.dumps(examples, ensure_ascii=False))
    stdlib = ROOT / "crates/deppy-python/stdlib"
    with zipfile.ZipFile(OUTPUT / "deppy-runtime.zip", "w", zipfile.ZIP_DEFLATED) as archive:
        for path in sorted((stdlib / "deppy").rglob("*.py")):
            archive.write(path, path.relative_to(stdlib))
    print(f"Built static demo in {OUTPUT}")


if __name__ == "__main__":
    main()
