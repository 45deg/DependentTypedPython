def builtin(declaration):
    # Ordinary Python helper; the static loader reads only @builtin declarations.
    from deppy._runtime import builtin as implementation
    return implementation(declaration)


# Proof tactics are compiler forms; their calls elaborate to checked terms.
# Their result types depend on the surrounding proof goal.

@builtin
def intro(body: object) -> object: ...

@builtin
def exact(proof: object) -> object: ...

@builtin
def apply(function: object, *args: object) -> object: ...

@builtin
def rewrite(equality: object, proof: object) -> object: ...

@builtin
def rewrite_in(equality: object, proof: object) -> object: ...

@builtin
def cases(value: object, branches: object) -> object: ...

@builtin
def induction(level: int, value: object, motive: object, *branches: object) -> object: ...
