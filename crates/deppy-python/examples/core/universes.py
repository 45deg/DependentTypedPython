from deppy import dependent, record, Type, Nat, Z, S


@record(level=1)
class Package:
    carrier: Type
    value: self.carrier


@dependent(decreases="n", motive_level=1)
def carrier(n: Nat) -> Type:
    match n:
        case Z():
            return Nat
        case S(k):
            return carrier(k)


@dependent
def unpack(n: Nat) -> Nat:
    package = Package(carrier(2), n)
    return package.value
