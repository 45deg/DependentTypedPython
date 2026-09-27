from deppy import dependent, record, Type, Nat, Sigma, Pair, Vec


@record
class SomeVec[T: Type]:
    n: Nat
    value: Vec[T, self.n]


@dependent
def pack[T: Type](n: Nat, xs: Vec[T, n]) -> Sigma[Nat, lambda k: Vec[T, k]]:
    return Pair(n, xs)


@dependent
def as_record[T: Type](p: Sigma[Nat, lambda k: Vec[T, k]]) -> SomeVec[T]:
    return SomeVec(p.fst, p.snd)


@dependent
def as_pair[T: Type](r: SomeVec[T]) -> Sigma[Nat, lambda k: Vec[T, k]]:
    return Pair(r.n, r.value)
