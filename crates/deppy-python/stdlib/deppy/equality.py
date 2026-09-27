from deppy._builtins import dependent, Type, Pi, Eq, refl, J


@dependent
def sym[A: Type, x: A, y: A](p: Eq[A, x, y]) -> Eq[A, y, x]:
    r"""Symmetry of equality: from :math:`x = y`, derive :math:`y = x`."""
    return J(0, A, x, lambda end, proof: Eq[A, end, x], refl(x), y, p)


@dependent
def trans[A: Type, x: A, y: A, z: A](p: Eq[A, x, y], q: Eq[A, y, z]) -> Eq[A, x, z]:
    r"""Transitivity of equality: :math:`x = y` and :math:`y = z` imply :math:`x = z`."""
    return J(0, A, y, lambda end, proof: Eq[A, x, end], p, z, q)


@dependent
def cong[A: Type, B: Type, x: A, y: A](f: Pi[A, lambda arg: B], p: Eq[A, x, y]) -> Eq[B, f(x), f(y)]:
    r"""Function congruence: :math:`x = y \Rightarrow f(x) = f(y)`."""
    return J(0, A, x, lambda end, proof: Eq[B, f(x), f(end)], refl(f(x)), y, p)


@dependent
def transport[A: Type, x: A, y: A](P: Pi[A, lambda arg: Type], p: Eq[A, x, y], value: P(x)) -> P(y):
    r"""Transport ``value`` from :math:`P(x)` to :math:`P(y)` along :math:`x = y`."""
    return J(0, A, x, lambda end, proof: P(end), value, y, p)


@dependent
def cong2[A: Type, B: Type, C: Type, x1: A, x2: A, y1: B, y2: B](
    f: Pi[A, lambda _: Pi[B, lambda _: C]],
    px: Eq[A, x1, x2],
    py: Eq[B, y1, y2],
) -> Eq[C, f(x1)(y1), f(x2)(y2)]:
    r"""Binary congruence: equal inputs give equal outputs for a curried function."""
    return trans(cong(lambda x: f(x)(y1), px), cong(lambda y: f(x2)(y), py))


@dependent
def transport_refl[A: Type, x: A](P: Pi[A, lambda _: Type], value: P(x)) -> Eq[P(x), transport(P, refl(x), value), value]:
    r"""Theorem ``transport_refl``: transport along reflexivity is the identity."""
    return refl(value)


@dependent
def transport_trans[A: Type, x: A, y: A, z: A](
    P: Pi[A, lambda _: Type], p: Eq[A, x, y], q: Eq[A, y, z], value: P(x)
) -> Eq[P(z), transport(P, q, transport(P, p, value)), transport(P, trans(p, q), value)]:
    r"""Theorem ``transport_trans``: successive transports equal transport along composition."""
    return J(
        0, A, y,
        lambda end, proof: Eq[P(end), transport(P, proof, transport(P, p, value)), transport(P, trans(p, proof), value)],
        refl(transport(P, p, value)), z, q,
    )
