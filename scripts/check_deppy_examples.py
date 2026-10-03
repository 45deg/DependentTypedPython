"""Check DepPy examples through the CLI without executing them as Python."""

import os
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "crates/deppy-python/examples/core"
PROOF_CASE = ROOT / "crates/deppy-python/examples/proof_case"
STDLIB = ROOT / "crates/deppy-python/stdlib/deppy"
CHECKS = 0


def binary() -> Path:
    override = os.environ.get("DEPPY_BIN")
    if override:
        return Path(override).resolve()
    subprocess.run(
        ["cargo", "build", "-p", "deppy-python", "--locked"],
        cwd=ROOT,
        check=True,
    )
    target = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
    return target / "debug" / ("deppy-python.exe" if os.name == "nt" else "deppy-python")


def run(executable: Path, path: Path, *args: str) -> subprocess.CompletedProcess[str]:
    command = [str(executable), *(["eval"] if args else []), str(path), *args]
    return subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False)


def accepted(
    executable: Path,
    path: Path,
    *,
    axiom_free: bool = False,
    names: tuple[str, ...] = (),
) -> None:
    global CHECKS
    result = run(executable, path)
    assert result.returncode == 0, f"{path}: {result.stderr}"
    if axiom_free:
        assert "[axioms:" not in result.stdout, f"{path}: {result.stdout}"
    for name in names:
        assert f"checked {name} [" in result.stdout, f"{path}: missing {name}"
    CHECKS += 1


def evaluated(executable: Path, path: Path, name: str, expected: str) -> None:
    global CHECKS
    result = run(executable, path, name)
    assert result.returncode == 0, f"{path} {name}: {result.stderr}"
    assert result.stdout.strip() == expected, f"{path} {name}: {result.stdout}"
    CHECKS += 1


def evaluated_refl(executable: Path, path: Path, name: str) -> None:
    global CHECKS
    result = run(executable, path, name)
    assert result.returncode == 0, f"{path} {name}: {result.stderr}"
    assert result.stdout.startswith("refl("), f"{path} {name}: {result.stdout}"
    CHECKS += 1


def rejected(
    executable: Path,
    source: str,
    label: str,
    *,
    forbidden: tuple[str, ...] = (),
) -> None:
    global CHECKS
    with tempfile.TemporaryDirectory(prefix="deppy-example-") as directory:
        path = Path(directory) / "case.py"
        path.write_text(source)
        result = run(executable, path)
    assert result.returncode == 1, f"{label}: expected rejection, got {result.returncode}: {result.stdout} {result.stderr}"
    assert result.stderr.strip(), f"{label}: missing diagnostic"
    for word in forbidden:
        assert word not in result.stderr, f"{label}: unexpected {word}: {result.stderr}"
    CHECKS += 1


def mutation(
    executable: Path,
    path: Path,
    old: str,
    new: str,
    *,
    forbidden: tuple[str, ...] = (),
) -> None:
    source = path.read_text()
    assert source.count(old) == 1, f"{path}: expected one mutation site"
    rejected(executable, source.replace(old, new), path.name, forbidden=forbidden)


def main() -> None:
    executable = binary()
    examples = (
        "indexed_matches.py",
        "nested_matches.py",
        "list_patterns.py",
        "list_induction.py",
        "list_recursion.py",
        "indexed_get.py",
        "docstrings.py",
        "tree_size.py",
        "indexed_length.py",
        "nested_indexed_get.py",
        "tree_depth.py",
        "list_theorems.py",
        "order_bounds.py",
        "order_absurd.py",
        "higher_universe.py",
    )
    for name in examples:
        accepted(executable, CORE / name, axiom_free=name.startswith("order_"))
    quicksort = CORE / "quicksort.py"
    accepted(executable, quicksort, axiom_free=True,
             names=("Sorted", "quicksort", "quicksort_sorted"))
    for name in ("empty_example", "singleton_example", "descending_example",
                 "ordered_example", "duplicates_example"):
        evaluated_refl(executable, quicksort, name)
    mutation(executable, quicksort, "return Pair(above, right)",
             "return Pair(MkUnit(), right)", forbidden=("budget", "import"))
    mutation(executable, quicksort,
             "return quicksort_bounded(length(xs), xs, le_refl(length(xs)))",
             "return quicksort_bounded(0, xs, le_refl(0))",
             forbidden=("budget", "import"))
    for name in ("data", "equality", "nat", "nat_order", "lists", "indexed"):
        accepted(executable, STDLIB / f"{name}.py", axiom_free=True)
    accepted(
        executable,
        STDLIB / "bool.py",
        axiom_free=True,
        names=(
            "negate_involutive",
            "conjunction_distrib",
            "disjunction_distrib",
            "negate_conjunction",
            "negate_disjunction",
            "is_true_intro",
            "is_true_elim",
            "eq_decide",
        ),
    )
    accepted(executable, PROOF_CASE / "cantor.py", axiom_free=True, names=("cantor",))
    regular_languages = ROOT / "web-demo/examples/proof_regular_languages.py"
    accepted(executable, regular_languages, axiom_free=True,
             names=("determinize", "nfa_to_dfa", "dfa_to_nfa", "determinize_correct", "one_has_nfa_path"))
    for name in ("empty_rejected", "one_accepted", "one_zero_rejected", "zero_one_accepted",
                 "both_branches_kept", "empty_subset_stays_empty"):
        evaluated_refl(executable, regular_languages, name)
    mutation(executable, regular_languages,
             "return lambda r: some(n)(lambda q: conjunction(get(n, subset, q), machine.edge(q)(symbol)(r)))",
             "return lambda r: some(n)(lambda q: machine.edge(q)(symbol)(r))",
             forbidden=("budget", "import"))
    mutation(executable, regular_languages, "        machine.initial,",
             "        tabulate(n)(lambda q: False_()),", forbidden=("budget", "import"))

    for file, name, expected in (
        ("indexed_matches.py", "proof", "refl(9)"),
        ("nested_matches.py", "proof", "refl(2)"),
        ("list_patterns.py", "selected", "refl(2)"),
        ("list_induction.py", "test", "refl(1)"),
        ("list_recursion.py", "proof", "refl(0)"),
        ("indexed_get.py", "first", "refl(7)"),
        ("indexed_get.py", "second", "refl(9)"),
        ("tree_size.py", "proof", "refl(3)"),
        ("indexed_length.py", "proof", "refl(1)"),
        ("nested_indexed_get.py", "proof", "refl(9)"),
        ("tree_depth.py", "proof", "refl(1)"),
    ):
        evaluated(executable, CORE / file, name, expected)
    for name in ("assoc", "identity", "composition", "involution"):
        evaluated_refl(executable, CORE / "list_theorems.py", name)

    mutation(executable, CORE / "indexed_matches.py", "return head(Z(), tail)", "return head(S(Z()), tail)")
    mutation(executable, CORE / "nested_matches.py", "                        case Cons(k, tail):\n                            return 3\n", "")
    mutation(executable, CORE / "list_patterns.py", "return pairs(rest)", "return pairs(xs)")
    mutation(executable, CORE / "indexed_get.py", "IFS(S(Z()), IFZ(Z()))", "IFS(S(S(Z())), IFZ(S(Z())))")
    mutation(executable, CORE / "tree_size.py", "size(left), size(right)", "size(tree), size(right)")
    mutation(executable, CORE / "list_theorems.py", "Cons(2, Nil[Nat]())", "Cons(1, Nil[Nat]())")
    mutation(executable, CORE / "higher_universe.py", "@inductive(level=1)", "@inductive")
    mutation(executable, PROOF_CASE / "cantor.py", "lambda x: negate(f(x)(x))", "lambda x: f(x)(x)", forbidden=("budget",))

    boolean_header = "from deppy import dependent, Eq, refl, Nat\nfrom deppy.bool import Bool, False_, True_, negate, conjunction, disjunction, xor, eq_decide\nfrom deppy.data import decision_weight\n"
    boolean = lambda value: "True_()" if value else "False_()"
    truth_table = [boolean_header]
    index = 0
    for a in (False, True):
        av = boolean(a)
        negated = boolean(not a)
        truth_table.append(f"@dependent\ndef neg_{index}() -> Eq[Bool, negate({av}), {negated}]:\n    return refl({negated})\n")
        for b in (False, True):
            bv = boolean(b)
            for operation, expected in (("conjunction", a and b), ("disjunction", a or b), ("xor", a ^ b)):
                value = boolean(expected)
                truth_table.append(f"@dependent\ndef table_{index}() -> Eq[Bool, {operation}({av}, {bv}), {value}]:\n    return refl({value})\n")
                index += 1
            weight = int(a == b)
            truth_table.append(f"@dependent\ndef decision_{index}() -> Eq[Nat, decision_weight(eq_decide({av}, {bv})), {weight}]:\n    return refl({weight})\n")
    with tempfile.TemporaryDirectory(prefix="deppy-example-") as directory:
        path = Path(directory) / "bool_table.py"
        path.write_text("\n".join(truth_table))
        accepted(executable, path)
    for expression in ("negate(False_())", "conjunction(True_(), True_())", "disjunction(False_(), True_())", "xor(False_(), True_())"):
        rejected(executable, boolean_header + f"@dependent\ndef invalid() -> Eq[Bool, {expression}, False_()]:\n    return refl(False_())\n", expression, forbidden=("budget", "import"))

    rejected(executable, "from deppy import inductive, constructor, Pi, Nat\n@inductive\nclass Bad:\n    @constructor\n    def Mk(f: Pi[Bad, Nat]) -> Bad: ...\n", "negative recursion")
    rejected(executable, "from deppy import inductive, constructor, dependent, Type, Pi, Nat\n@dependent\ndef Negative(T: Type) -> Type:\n    return Pi[T, lambda _: Nat]\n@inductive\nclass Bad:\n    @constructor\n    def Mk(f: Negative(Bad)) -> Bad: ...\n", "negative alias")

    indexed_header = "from deppy import dependent, Nat, Z, S, absurd\nfrom deppy.indexed import IFin\n"
    for params, bound, should_accept in (("", "Z()", True), ("", "S(Z())", False), ("n: Nat, ", "n", False)):
        source = indexed_header + f"@dependent\ndef impossible({params}i: IFin[{bound}]) -> Nat:\n    return absurd(Nat, i)\n"
        if should_accept:
            with tempfile.TemporaryDirectory(prefix="deppy-example-") as directory:
                path = Path(directory) / "case.py"
                path.write_text(source)
                accepted(executable, path)
        else:
            rejected(executable, source, f"indexed absurd {bound}")

    order_header = (CORE / "order_bounds.py").read_text().split("\n@dependent", 1)[0] + "\n"
    decisions = []
    for n in range(4):
        for m in range(4):
            for name, expected in (("le_decide", n <= m), ("lt_decide", n < m)):
                value = int(expected)
                decisions.append(f"@dependent\ndef {name}_{n}_{m}() -> Eq[Nat, decision_weight({name}({n}, {m})), {value}]:\n    return refl({value})\n")
    with tempfile.TemporaryDirectory(prefix="deppy-example-") as directory:
        path = Path(directory) / "decisions.py"
        path.write_text(order_header + "\n".join(decisions))
        accepted(executable, path, axiom_free=True)
    rejected(executable, order_header + "@dependent\ndef bad() -> Eq[Nat, decision_weight(le_decide(2, 1)), 1]:\n    return refl(1)\n", "wrong order decision")
    for body in (
        "def bad(n: Nat) -> LT(n, n):\n    return le_refl(n)",
        "def bad() -> LT(pred_or(0, 0), 0):\n    return pred_lt(0, le_refl(0))",
        "def bad(n: Nat, m: Nat, p: LE[n, m]) -> LE[S(n), m]:\n    return le_step(p)",
    ):
        rejected(executable, order_header + "@dependent\n" + body + "\n", body.split("(", 1)[0])
    for ty in ("LE[0, n]", "LE[n, n]", "LE[S(n), S(n)]", "LE[n, 0]", "Nat"):
        rejected(executable, order_header + f"@dependent\ndef bad(n: Nat, p: {ty}) -> Empty:\n    return absurd(Empty, p)\n", f"absurd {ty}")

    print(f"{CHECKS} DepPy CLI example checks passed")


if __name__ == "__main__":
    main()
