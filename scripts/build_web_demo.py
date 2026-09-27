"""Build the client-only DepPy playground assets."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "web-demo"
EXAMPLES = {
    "basics": ("Basics", "core/basics.py"),
    "proofs": ("Proofs", "core/proofs.py"),
    "verified": ("Verified", "verified/verified_annotations.py"),
}


def main() -> None:
    subprocess.run(
        ["cargo", "build", "-p", "deppy-web", "--target", "wasm32-unknown-unknown", "--release", "--locked", "--offline"],
        cwd=ROOT,
        check=True,
    )
    shutil.copyfile(ROOT / "target/wasm32-unknown-unknown/release/deppy_web.wasm", OUTPUT / "checker.wasm")
    examples = {
        key: {"label": label, "source": (ROOT / "crates/deppy-python/examples" / filename).read_text()}
        for key, (label, filename) in EXAMPLES.items()
    }
    (OUTPUT / "examples.json").write_text(json.dumps(examples, ensure_ascii=False))
    print(f"Built static demo in {OUTPUT}")


if __name__ == "__main__":
    main()
