from __future__ import annotations

from deppy._builtins import dependent, theorem, Type, Eq, refl, absurd
from deppy.data import Bool, False_, True_, Empty, Unit, MkUnit, Decidable, Yes, No
from deppy.equality import sym, transport


@dependent
def negate(b: Bool) -> Bool:
    """Exchange the two Boolean values."""
    match b:
        case False_():
            return True_()
        case True_():
            return False_()


@dependent(decreases="b", motive_level=1)
def is_true(b: Bool) -> Type:
    """A proposition inhabited exactly when b is true."""
    match b:
        case False_():
            return Empty
        case True_():
            return Unit


@dependent
def conjunction(a: Bool, b: Bool) -> Bool:
    """Boolean conjunction (and)."""
    match a:
        case False_():
            return False_()
        case True_():
            return b


@dependent
def disjunction(a: Bool, b: Bool) -> Bool:
    """Boolean disjunction (or)."""
    match a:
        case False_():
            return b
        case True_():
            return True_()


@dependent
def xor(a: Bool, b: Bool) -> Bool:
    """Exclusive disjunction: true exactly when the inputs differ."""
    match a:
        case False_():
            return b
        case True_():
            return negate(b)


@theorem
def true_ne_false(equal: Eq[Bool, True_(), False_()]) -> Empty:
    """The Boolean constructors are distinct."""
    return transport[Bool, True_(), False_()](is_true, equal, MkUnit())


@dependent(decreases="a")
def eq_decide(a: Bool, b: Bool) -> Decidable[Eq[Bool, a, b]]:
    """Decide Boolean equality with a proof or a refutation."""
    match a:
        case False_():
            match b:
                case False_():
                    return Yes[Eq[Bool, False_(), False_()]](refl(False_()))
                case True_():
                    return No[Eq[Bool, False_(), True_()]](lambda p: true_ne_false(sym(p)))
        case True_():
            match b:
                case False_():
                    return No[Eq[Bool, True_(), False_()]](lambda p: true_ne_false(p))
                case True_():
                    return Yes[Eq[Bool, True_(), True_()]](refl(True_()))


@theorem(decreases="b")
def is_true_intro(b: Bool, equal: Eq[Bool, b, True_()]) -> is_true(b):
    """Equality to true supplies evidence of the Boolean proposition."""
    return transport[Bool, True_(), b](is_true, sym(equal), MkUnit())


@theorem(decreases="b")
def is_true_elim(b: Bool, proof: is_true(b)) -> Eq[Bool, b, True_()]:
    """Evidence of the Boolean proposition implies equality to true."""
    match b:
        case False_():
            return absurd(Eq[Bool, False_(), True_()], proof)
        case True_():
            return refl(True_())


@theorem(decreases="a")
def negate_involutive(a: Bool) -> Eq[Bool, negate(negate(a)), a]:
    """Prove ``negate(negate(a)) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def conjunction_identity(a: Bool) -> Eq[Bool, conjunction(a, True_()), a]:
    """Prove ``conjunction(a, True_()) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def conjunction_annihilator(a: Bool) -> Eq[Bool, conjunction(a, False_()), False_()]:
    """Prove ``conjunction(a, False_()) = False_()``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(False_())


@theorem(decreases="a")
def conjunction_idempotent(a: Bool) -> Eq[Bool, conjunction(a, a), a]:
    """Prove ``conjunction(a, a) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def conjunction_complement(a: Bool) -> Eq[Bool, conjunction(a, negate(a)), False_()]:
    """Prove ``conjunction(a, negate(a)) = False_()``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(False_())


@theorem(decreases="a")
def conjunction_comm(a: Bool, b: Bool) -> Eq[Bool, conjunction(a, b), conjunction(b, a)]:
    """Prove ``conjunction(a, b) = conjunction(b, a)``."""
    match a:
        case False_():
            match b:
                case False_():
                    return refl(conjunction(False_(), False_()))
                case True_():
                    return refl(conjunction(True_(), False_()))
        case True_():
            match b:
                case False_():
                    return refl(conjunction(False_(), True_()))
                case True_():
                    return refl(conjunction(True_(), True_()))


@theorem(decreases="a")
def conjunction_assoc(a: Bool, b: Bool, c: Bool) -> Eq[Bool, conjunction(conjunction(a, b), c), conjunction(a, conjunction(b, c))]:
    """Prove ``conjunction(conjunction(a, b), c) = conjunction(a, conjunction(b, c))``."""
    match a:
        case False_():
            return refl(conjunction(False_(), conjunction(b, c)))
        case True_():
            return refl(conjunction(True_(), conjunction(b, c)))


@theorem(decreases="a")
def disjunction_identity(a: Bool) -> Eq[Bool, disjunction(a, False_()), a]:
    """Prove ``disjunction(a, False_()) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def disjunction_annihilator(a: Bool) -> Eq[Bool, disjunction(a, True_()), True_()]:
    """Prove ``disjunction(a, True_()) = True_()``."""
    match a:
        case False_():
            return refl(True_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def disjunction_idempotent(a: Bool) -> Eq[Bool, disjunction(a, a), a]:
    """Prove ``disjunction(a, a) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def disjunction_complement(a: Bool) -> Eq[Bool, disjunction(a, negate(a)), True_()]:
    """Prove ``disjunction(a, negate(a)) = True_()``."""
    match a:
        case False_():
            return refl(True_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def disjunction_comm(a: Bool, b: Bool) -> Eq[Bool, disjunction(a, b), disjunction(b, a)]:
    """Prove ``disjunction(a, b) = disjunction(b, a)``."""
    match a:
        case False_():
            match b:
                case False_():
                    return refl(disjunction(False_(), False_()))
                case True_():
                    return refl(disjunction(True_(), False_()))
        case True_():
            match b:
                case False_():
                    return refl(disjunction(False_(), True_()))
                case True_():
                    return refl(disjunction(True_(), True_()))


@theorem(decreases="a")
def disjunction_assoc(a: Bool, b: Bool, c: Bool) -> Eq[Bool, disjunction(disjunction(a, b), c), disjunction(a, disjunction(b, c))]:
    """Prove ``disjunction(disjunction(a, b), c) = disjunction(a, disjunction(b, c))``."""
    match a:
        case False_():
            return refl(disjunction(False_(), disjunction(b, c)))
        case True_():
            return refl(disjunction(True_(), disjunction(b, c)))


@theorem(decreases="a")
def negate_conjunction(a: Bool, b: Bool) -> Eq[Bool, negate(conjunction(a, b)), disjunction(negate(a), negate(b))]:
    """Prove ``negate(conjunction(a, b)) = disjunction(negate(a), negate(b))``."""
    match a:
        case False_():
            return refl(disjunction(negate(False_()), negate(b)))
        case True_():
            return refl(disjunction(negate(True_()), negate(b)))


@theorem(decreases="a")
def conjunction_absorption(a: Bool, b: Bool) -> Eq[Bool, conjunction(a, disjunction(a, b)), a]:
    """Prove ``conjunction(a, disjunction(a, b)) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def conjunction_distrib(a: Bool, b: Bool, c: Bool) -> Eq[Bool, conjunction(a, disjunction(b, c)), disjunction(conjunction(a, b), conjunction(a, c))]:
    """Prove ``conjunction(a, disjunction(b, c)) = disjunction(conjunction(a, b), conjunction(a, c))``."""
    match a:
        case False_():
            return refl(disjunction(conjunction(False_(), b), conjunction(False_(), c)))
        case True_():
            return refl(disjunction(conjunction(True_(), b), conjunction(True_(), c)))


@theorem(decreases="a")
def negate_disjunction(a: Bool, b: Bool) -> Eq[Bool, negate(disjunction(a, b)), conjunction(negate(a), negate(b))]:
    """Prove ``negate(disjunction(a, b)) = conjunction(negate(a), negate(b))``."""
    match a:
        case False_():
            return refl(conjunction(negate(False_()), negate(b)))
        case True_():
            return refl(conjunction(negate(True_()), negate(b)))


@theorem(decreases="a")
def disjunction_absorption(a: Bool, b: Bool) -> Eq[Bool, disjunction(a, conjunction(a, b)), a]:
    """Prove ``disjunction(a, conjunction(a, b)) = a``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(True_())


@theorem(decreases="a")
def disjunction_distrib(a: Bool, b: Bool, c: Bool) -> Eq[Bool, disjunction(a, conjunction(b, c)), conjunction(disjunction(a, b), disjunction(a, c))]:
    """Prove ``disjunction(a, conjunction(b, c)) = conjunction(disjunction(a, b), disjunction(a, c))``."""
    match a:
        case False_():
            return refl(conjunction(disjunction(False_(), b), disjunction(False_(), c)))
        case True_():
            return refl(conjunction(disjunction(True_(), b), disjunction(True_(), c)))


@theorem(decreases="a")
def xor_self(a: Bool) -> Eq[Bool, xor(a, a), False_()]:
    """Prove ``xor(a, a) = False_()``."""
    match a:
        case False_():
            return refl(False_())
        case True_():
            return refl(False_())


@theorem(decreases="a")
def xor_comm(a: Bool, b: Bool) -> Eq[Bool, xor(a, b), xor(b, a)]:
    """Prove ``xor(a, b) = xor(b, a)``."""
    match a:
        case False_():
            match b:
                case False_():
                    return refl(xor(False_(), False_()))
                case True_():
                    return refl(xor(True_(), False_()))
        case True_():
            match b:
                case False_():
                    return refl(xor(False_(), True_()))
                case True_():
                    return refl(xor(True_(), True_()))
