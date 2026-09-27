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
