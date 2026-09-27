from deppy import dependent, Type, Pi, Nat, S, Eq, trans, Fin, fin0_elim, fin_case, Vec, VCons, vec_elim
from deppy.vectors import get, snoc, reverse, mirror, get_snoc_last, get_snoc_weaken


@dependent
def reverse_get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> Eq[
    T, get(n, reverse(n, xs), mirror(n, i)), get(n, xs, i),
]:
    return vec_elim(
        0, T,
        lambda size, ys: Pi[Fin[size], lambda j: Eq[
            T, get(size, reverse(size, ys), mirror(size, j)), get(size, ys, j),
        ]],
        lambda j: fin0_elim(j),
        lambda k, x, rest, ih: lambda j: fin_case(
            k,
            lambda q: Eq[
                T,
                get(S(k), snoc(k, x, reverse(k, rest)), mirror(S(k), q)),
                get(S(k), VCons(k, x, rest), q),
            ],
            j,
            get_snoc_last(k, x, reverse(k, rest)),
            lambda pred: trans(
                get_snoc_weaken(k, x, reverse(k, rest), mirror(k, pred)),
                ih(pred),
            ),
        ),
        n, xs,
    )(i)
