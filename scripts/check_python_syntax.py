"""Compile source fixtures without importing or executing them (CPython 3.14)."""
import pathlib
import sys

if sys.implementation.name != "cpython" or sys.version_info[:2] != (3, 14):
    raise SystemExit("CPython 3.14 is required")

root = pathlib.Path(__file__).resolve().parent.parent
paths = list((root / "crates/deppy-python/examples").rglob("*.py"))
paths += list((root / "crates/deppy-python/stdlib").rglob("*.py"))
for path in paths:
    compile(path.read_text(encoding="utf-8"), str(path), "exec", dont_inherit=True)
    print(f"compiled (not executed): {path.relative_to(root)}")
print(f"CPython {sys.version.split()[0]}: {len(paths)} fixtures passed")
