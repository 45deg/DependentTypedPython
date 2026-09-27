# Verification scope

The test suite covers core typing, elaboration, accepted and rejected examples, and runtime boundaries. Example checks include normalized results as well as diagnostics. These checks establish behavior for the covered cases, not general semantic preservation.

The verified numeric integration tests check the example and its imported GCD proof, then generate and execute six numeric functions. They compare subtraction and GCD with Python arithmetic and `math.gcd`, and check signed negation, floor division, and remainder across both signs and zero. The example's zero-divisor branches return zero. Int inputs use checked `lift` and `negate` exports; invalid boundary values are rejected.

`gcd_correct` remains statically checked but is not selected for runtime export: its proof computation uses erased arguments that extraction cannot retain. These finite execution checks do not establish general semantic preservation.

The syntax check compiles source without executing programs or checking proofs. Runtime differential checks compare fixtures with a test-only reference model. The documentation generator extracts curated declarations, complete signatures, and docstrings statically without running proof files.
