# Documentation

Start with the [project README](../README.md). English is the canonical documentation language; the [Japanese summary](ja/README.md) covers the essentials.

## Language specifications

1. [Core, frontend, and runtime](reference.md) — architecture, typing rules, elaboration, static Python input, and public runtime boundary.
2. [Proofs](proofs.md) — proof syntax, imports, axioms, holes, erasure, and tactics.
3. [Inductive families](inductives.md) — declarations, indexed patterns, recursion, and inductive runtime values.
4. [Verified programs](verified.md) — contracts, VCs, expressions, loops, refinements, and specification reuse.
5. [Mathematical library](math-library.md) — available modules and API design rules.

6. [Python source execution](python-runtime.md) — package installation, editor imports, direct execution, and its limits.

## Reference and project work

- [Generated mathematical API](index.rst) — Sphinx entry point for docstrings.
- [Verification scope](development.md) — coverage and the limits of each check.
- [Roadmap](roadmap.md) — unsupported features and acceptance criteria for proposed extensions.
- [Standard-library plan](stdlib-plan.md) — implemented coverage, API inconsistencies, missing foundations, and ordered extension proposals.

Keep accepted behavior in its specification and proposed behavior in the roadmap. Update the relevant page when support changes; do not add dated implementation logs or historical test counts.
