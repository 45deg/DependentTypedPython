from __future__ import annotations

# Proof tactics are compiler forms; their calls elaborate to checked terms.

@builtin
def intro(body): ...

@builtin
def exact(proof): ...

@builtin
def apply(function, *args): ...

@builtin
def rewrite(equality, proof): ...

@builtin
def rewrite_in(equality, proof): ...

@builtin
def cases(value, branches): ...

@builtin
def induction(level, value, motive, *branches): ...
