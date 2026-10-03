from deppy import dependent, theorem, record, Type, Pi, Eq, refl, cong, sym, trans


# Part 6: the kernel of a group homomorphism is a subgroup.
# A group is supplied with its laws; none of those laws is assumed globally.
# Write x · y for g.op(x)(y), e for g.unit, and x⁻¹ for g.inverse(x).
# We prove e ∈ ker(f), then closure under · and ⁻¹.


@record
class Group[A: Type]:
    unit: A
    op: Pi[A, lambda x: Pi[A, lambda y: A]]
    inverse: Pi[A, lambda x: A]
    assoc: Pi[A, lambda x: Pi[A, lambda y: Pi[A, lambda z:
        Eq[A, self.op(self.op(x)(y))(z), self.op(x)(self.op(y)(z))]]]]
    left_unit: Pi[A, lambda x: Eq[A, self.op(self.unit)(x), x]]
    right_unit: Pi[A, lambda x: Eq[A, self.op(x)(self.unit), x]]
    left_inverse: Pi[A, lambda x: Eq[A, self.op(self.inverse(x))(x), self.unit]]
    right_inverse: Pi[A, lambda x: Eq[A, self.op(x)(self.inverse(x)), self.unit]]


@record
class Hom[A: Type, B: Type, g: Group[A], h: Group[B]]:
    # f(x · y) = f(x) · f(y), and f(e_G) = e_H.
    map: Pi[A, lambda x: B]
    mul: Pi[A, lambda x: Pi[A, lambda y:
        Eq[B, self.map(g.op(x)(y)), h.op(self.map(x))(self.map(y))]]]
    unit: Eq[B, self.map(g.unit), h.unit]


@theorem
def inverse_unique[A: Type](g: Group[A], a: A, x: A, left: Eq[A, g.op(x)(a), g.unit]) -> Eq[A, x, g.inverse(a)]:
    # If x · a = e, then x = x · e = x · (a · a⁻¹) = (x · a) · a⁻¹ = a⁻¹.
    return trans(
        sym(g.right_unit(x)),
        trans(
            cong(lambda y: g.op(x)(y), sym(g.right_inverse(a))),
            trans(
                sym(g.assoc(x)(a)(g.inverse(a))),
                trans(
                    cong(lambda y: g.op(y)(g.inverse(a)), left),
                    g.left_unit(g.inverse(a)),
                ),
            ),
        ),
    )


@theorem
def map_inverse[A: Type, B: Type](g: Group[A], h: Group[B], f: Hom[A, B, g, h], a: A) -> Eq[B, f.map(g.inverse(a)), h.inverse(f.map(a))]:
    # f(a⁻¹) · f(a) = f(a⁻¹ · a) = f(e_G) = e_H.
    product_is_unit = trans(
        sym(f.mul(g.inverse(a))(a)),
        trans(cong(f.map, g.left_inverse(a)), f.unit),
    )
    # A left inverse is unique, so f(a⁻¹) = f(a)⁻¹.
    return inverse_unique(h, f.map(a), f.map(g.inverse(a)), product_is_unit)


@theorem
def inverse_unit[A: Type](g: Group[A]) -> Eq[A, g.inverse(g.unit), g.unit]:
    # e⁻¹ · e = e and e⁻¹ · e = e⁻¹, hence e⁻¹ = e.
    return trans(sym(g.right_unit(g.inverse(g.unit))), g.left_inverse(g.unit))


@dependent
def InKernel[A: Type, B: Type](g: Group[A], h: Group[B], f: Hom[A, B, g, h], a: A) -> Type:
    # ker(f) = {a ∈ G | f(a) = e_H}.
    return Eq[B, f.map(a), h.unit]


@theorem
def kernel_unit[A: Type, B: Type](g: Group[A], h: Group[B], f: Hom[A, B, g, h]) -> InKernel(g, h, f, g.unit):
    # e_G ∈ ker(f).
    return f.unit


@theorem
def kernel_mul[A: Type, B: Type](g: Group[A], h: Group[B], f: Hom[A, B, g, h], a: A, b: A, pa: InKernel(g, h, f, a), pb: InKernel(g, h, f, b)) -> InKernel(g, h, f, g.op(a)(b)):
    # f(a · b) = f(a) · f(b) = e_H · e_H = e_H.
    return trans(
        f.mul(a)(b),
        trans(
            cong(lambda x: h.op(x)(f.map(b)), pa),
            trans(cong(lambda x: h.op(h.unit)(x), pb), h.left_unit(h.unit)),
        ),
    )


@theorem
def kernel_inverse[A: Type, B: Type](g: Group[A], h: Group[B], f: Hom[A, B, g, h], a: A, pa: InKernel(g, h, f, a)) -> InKernel(g, h, f, g.inverse(a)):
    # f(a⁻¹) = f(a)⁻¹ = e_H⁻¹ = e_H.
    return trans(map_inverse(g, h, f, a), trans(cong(h.inverse, pa), inverse_unit(h)))


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    # A concrete homomorphism Z/4Z -> Z/2Z: send x to x mod 2.
    # These Python records illustrate the operations; Check verifies the
    # generic theorem above, given group laws and homomorphism laws.
    def cyclic_group(modulus):
        op = lambda x: lambda y: (x + y) % modulus
        inverse = lambda x: (-x) % modulus
        return Group(0, op, inverse,
            lambda x: lambda y: lambda z: refl(op(op(x)(y))(z)),
            lambda x: refl(x), lambda x: refl(x),
            lambda x: refl(0), lambda x: refl(0))

    g, h = cyclic_group(4), cyclic_group(2)
    f = Hom(lambda x: x % 2, lambda x: lambda y: refl((x + y) % 2), refl(0))
    kernel = [x for x in range(4) if f.map(x) == h.unit]
    print(f"ker(x mod 2) in Z/4Z = {kernel}")
    print(f"unit in kernel: {g.unit in kernel}")
    print(f"closed under addition: {all(g.op(x)(y) in kernel for x in kernel for y in kernel)}")
    print(f"closed under inverse: {all(g.inverse(x) in kernel for x in kernel)}")
