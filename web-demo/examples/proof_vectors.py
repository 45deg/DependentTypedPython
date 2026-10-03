from deppy import dependent, Type, Nat, Vec, VNil, VCons, Fin, FZ, FS, fin0_elim


# Part 3: an index Fin[n] witnesses that a position is inside Vec[T, n].
# A well-typed call to get therefore has no out-of-bounds case.


@dependent(decreases="xs")
def get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> T:
    # Input: xs has length n and i ∈ {0, …, n − 1}. Output: an element of T.
    match xs:
        case VNil():
            # n = 0 ⇒ i : Fin[0]. No such index exists; eliminate it.
            return fin0_elim(i)
        case VCons(k, x, rest):
            # n = S(k). Split the index into the head or a tail position.
            match i:
                case FZ(_):
                    # Position 0 → the head x.
                    return x
                case FS(_, j):
                    # Position S(j) → recurse into the length-k tail.
                    return get(k, rest, j)


if __name__ == "__main__":
    # Run executes these concrete examples; Check verifies the declarations above.
    values = VCons(2, 10, VCons(1, 20, VCons(0, 30, VNil())))
    print(f"get([10, 20, 30], 0) = {get(3, values, FZ(2))}")
    print(f"get([10, 20, 30], 1) = {get(3, values, FS(2, FZ(1)))}")
    print(f"get([10, 20, 30], 2) = {get(3, values, FS(2, FS(1, FZ(0))))}")
