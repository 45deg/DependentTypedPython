# Roadmap

The [documentation index](README.md) links the accepted specifications. This page records unsupported features and the criteria for proposed extensions. A proposal below does not change the accepted language.

## Open work

| Area | Work |
| --- | --- |
| Elaboration | Keyword selection of implicit arguments, deferred constraint retry, metavariable pruning, broader unification, and semantic-value/closure evaluation |
| Type theory and patterns | Universe polymorphism, mutual inductives, nested recursion through existing type constructors, and indexed patterns with nonlinear or neutral function applications |
| Verified programs | Contract calls in `while` guards; general Int bounds and dynamic negative steps for `range`; lexicographic measures and general well-founded relations; invariant inference beyond local `Refined` annotations; combining safety conditions in guards or measures with a single `proof=`; broader arithmetic proof search; cross-base refinement conversions |
| Mathematics | Shared removal evidence and public API cleanup; Option/decision helpers, Fin construction and standard enumerations, Vec/List interoperability, integer laws, and promotion of algebra/finite products; see the [standard-library plan](stdlib-plan.md) |
| Runtime and compatibility | External Python proof inputs, `Proof[...]`, arbitrary type-family schemas or public boundaries needing erased information, source-compatible record classes, and CPython 3.13 runtime checks |
| Assurance | General semantic preservation from CPython source to Verified HIR and from checked terms to extracted code; stack and memory guarantees for deep recursion |

Implicit refinement subtyping, general higher-order unification, and complete automatic proof search are outside the current scope. Generated Python execution for verified numeric examples remains unverified because extraction's proof-erasure pass exceeds the default budget. The relevant reproducible checks are in [development.md](development.md).

## Acceptance criteria for verified extensions

### Contract calls in `while` guards

Evaluate guard calls in order on every iteration. Prove each precondition from the invariant and current state, then use the checked postcondition to reason about the guard result. Preserve termination and exit obligations. Give multiple calls distinct goals and original source locations; do not unfold the callee or assume its precondition.

### General numeric `range`

Specify iteration and empty-range behavior for Int bounds and dynamic negative steps, including the step sign and nonzero condition. Generate safety, invariant, and termination VCs. Preserve simultaneous-assignment semantics and source positions for calls in bounds or the body.

### Measures and invariant inference

Check lexicographic tuples and explicit well-founded relations, rejecting nondecreasing iterations and circular contract justification. Any inferred invariant must have proved initialization and preservation before use.

### Composite values and verified recursion

Share checked standard-library tuples, finite sequences, lists, options, and indexed types instead of adding parallel representations. Constructor branches must expose field and index facts to VCs. Fixed-size array reads need Fin or a range VC. Recursive verified functions need a checked decrease and contracts that cannot justify themselves cyclically.

### Optional strings and automation

Define Unicode representation, length, indexing, slicing, concatenation, and bounds before accepting strings. Cover empty and non-ASCII cases; require range proofs for reads. Regex, encoding conversion, and locale behavior are outside this proposal. Any added proof search must still produce core terms checked by the kernel. Runtime checks and semantic preservation remain separate work.
