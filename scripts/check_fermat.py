"""Check the Fermat proof and reject two corrupted proofs without running them.

Build the checker first with `cargo build -p deppy-python --locked --offline`.
This script uses only the Python standard library.
"""

import argparse
import pathlib
import subprocess
import tempfile


def main():
    root = pathlib.Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker", type=pathlib.Path, default=root / "target/debug/deppy-python")
    parser.add_argument("--elaboration-steps", type=int, default=100_000_000)
    args = parser.parse_args()
    if args.elaboration_steps <= 0:
        parser.error("--elaboration-steps must be positive")
    checker = args.checker.resolve()
    examples = root / "crates/deppy-python/examples"
    source = (examples / "fermat.py").read_text(encoding="utf-8")

    def check(path):
        return subprocess.run(
            [str(checker), "--elaboration-steps", str(args.elaboration_steps), str(path)],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )

    valid = check(examples / "fermat.py")
    if valid.returncode:
        raise AssertionError(valid.stderr)
    for name in ("finite_group_power", "fermat_little", "fermat_three", "fermat_three_two"):
        if f"checked {name} [axiom-free]" not in valid.stdout.splitlines():
            raise AssertionError(f"Missing axiom-free theorem: {name}")
    if "[axioms:" in valid.stdout:
        raise AssertionError(valid.stdout)
    print("PASS: general theorem and F_3 examples are axiom-free", flush=True)

    corruptions = (
        ("wrong exponent", "power(bit_group(), a, 2)", "power(bit_group(), a, 3)"),
        (
            "missing Lagrange argument",
            "return lagrange_power(g, h, finite, a, period)",
            "return refl(g.unit)",
        ),
    )
    with tempfile.TemporaryDirectory(prefix="deppy-fermat-") as temporary:
        folder = pathlib.Path(temporary)
        (folder / "lagrange.py").write_text(
            (examples / "lagrange.py").read_text(encoding="utf-8"), encoding="utf-8"
        )
        for name, before, after in corruptions:
            if source.count(before) != 1:
                raise AssertionError(f"Expected exactly one mutation site: {before}")
            path = folder / "fermat.py"
            path.write_text(source.replace(before, after), encoding="utf-8")
            invalid = check(path)
            if invalid.returncode == 0 or "checked fermat_little" in invalid.stdout:
                raise AssertionError(f"Accepted {name}")
            if "budget exhausted" in invalid.stderr or "expected " not in invalid.stderr:
                raise AssertionError(f"Did not reject {name} as a type error: {invalid.stderr}")
            print(f"PASS: rejected {name}", flush=True)


if __name__ == "__main__":
    main()
