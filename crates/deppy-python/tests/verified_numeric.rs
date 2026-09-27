use deppy_python::{analyze_module, check_module, Target};
const HEADER: &str = "from __future__ import annotations\nfrom deppy import Nat, Eq, refl, theorem\nfrom deppy.verified import verified, Refined\nfrom deppy.data import Bool, True_\nfrom deppy.nat_order import LE, LT\nfrom deppy.arithmetic import sub, quotient, remainder\nfrom deppy.verified_loop import decreases\n";
fn check(body: &str) {
    let source = format!("{HEADER}{body}");
    let checked =
        check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}\n{source}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}
#[test]
fn subtraction_and_division_compute() {
    check(
        r#"
@verified
def calc() -> Refined[Nat, lambda r: Eq[Nat, r, 5]]:
    x = 7 - 2
    x -= 1
    x += (7 // 3) * (7 % 3)
    return x - 1
"#,
    );
}
#[test]
fn decrement_loop_and_symbolic_bounds() {
    check(
        r#"
from deppy.arithmetic import sub_add
from deppy.nat import add
@verified(using=(sub_add,))
def diff(n: Nat, m: Refined[Nat, lambda m: LE(m, n)]) -> Refined[Nat, lambda r: Eq[Nat, add(m, r), n]]:
    return n - m
@verified
def countdown(n: Nat) -> Nat:
    x = n
    while 0 < x:
        decreases(x)
        x -= 1
    return x
"#,
    );
}
#[test]
fn unsafe_numeric_operations_are_rejected_with_source_goals() {
    for expression in ["0 - 1", "5 // 0", "5 % 0", "5 // n", "n - 1"] {
        let source =
            format!("{HEADER}@verified\ndef bad(n: Nat) -> Nat:\n    return {expression}\n");
        let result = analyze_module(&source, Target::Python314);
        assert!(result.checked.is_none());
        let goal = result
            .goals
            .iter()
            .find(|g| g.name.contains("arithmetic."))
            .unwrap_or_else(|| panic!("{:?}", result.diagnostics));
        let location = goal.location.as_ref().unwrap();
        assert_eq!(&source[location.start..location.end], expression);
    }
}
#[test]
fn signed_operations_and_conversion() {
    check(
        r#"
from deppy.integer import Int, Pos, Neg, of_nat, to_nat
@verified
def signed() -> Refined[Int, lambda r: Eq[Int, r, Neg(2)]]:
    x: Int = -7
    y: Int = 3
    return x // y
@verified
def rem() -> Refined[Int, lambda r: Eq[Int, r, Pos(2)]]:
    x: Int = -7
    return x % 3
@verified
def cast(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    x: Int = of_nat(n)
    return to_nat(x)
"#,
    );
}

#[test]
fn short_circuit_and_conditionals_check_only_reachable_arithmetic() {
    check(
        r#"
@verified
def selected(n: Nat, d: Nat) -> Nat:
    return 0 if d == 0 else n // d
@verified
def skipped() -> Bool:
    return False and (1 // 0 == 0)
@verified
def guarded(n: Nat, d: Nat) -> Bool:
    return d != 0 and n % d == 0
"#,
    );
}

#[test]
fn euclid_uses_the_checked_remainder_bound() {
    check(
        r#"
from deppy.nat import add, mul
from deppy.arithmetic import divmod_equation
@verified
def gcd(a: Nat, b: Nat) -> Nat:
    x = a
    y = b
    while 0 < y:
        decreases(y)
        x, y = y, x % y
    return x
@theorem
def quotient_remainder_law(n: Nat, d: Nat) -> Eq[Nat, add(mul(d, quotient(n, d)), remainder(n, d)), n]:
    return divmod_equation(n, d)
@theorem
def computes_gcd() -> Eq[Nat, gcd(4, 2), 2]:
    return refl(2)
"#,
    );
}

#[test]
fn signed_floor_division_all_signs_and_zero_boundaries() {
    // Rust's div_euclid has different semantics for a negative divisor;
    // derive the floor quotient explicitly for the test oracle.
    let mut source = "from deppy.integer import Int, Pos, Neg\n".to_owned();
    let repr = |n: i32| {
        if n >= 0 {
            format!("Pos({n})")
        } else {
            format!("Neg({})", -n - 1)
        }
    };
    for (i, (a, b)) in [
        (7, 3),
        (-7, 3),
        (7, -3),
        (-7, -3),
        (0, 3),
        (0, -3),
        (6, -3),
        (-6, 3),
        (1, 2),
        (-1, 2),
    ]
    .into_iter()
    .enumerate()
    {
        let q = (a as f64 / b as f64).floor() as i32;
        let r = a - b * q;
        source.push_str(&format!("@verified\ndef q{i}() -> Refined[Int, lambda r: Eq[Int, r, {}]]:\n    a: Int = {a}\n    return a // {b}\n@verified\ndef r{i}() -> Refined[Int, lambda r: Eq[Int, r, {}]]:\n    a: Int = {a}\n    return a % {b}\n", repr(q), repr(r)));
    }
    check(&source);
}

#[test]
fn signed_bad_conversions_mixed_values_and_zero_divisors_are_rejected() {
    for body in [
        "    x: Int = -1\n    return to_nat(x)",
        "    x: Int = 1\n    return to_nat(x // 0)",
        "    x: Int = 1\n    return to_nat(x % 0)",
        "    x: Int = 1\n    return to_nat(x + n)",
    ] {
        let source = format!("{HEADER}from deppy.integer import Int, to_nat\n@verified\ndef bad(n: Nat) -> Nat:\n{body}\n");
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{source}"
        );
    }
}

#[test]
fn explicit_arithmetic_proofs_are_checked_and_contracts_stay_abstract() {
    let source = format!("{HEADER}from deppy.data import False_\n@verified(proofs={{'arithmetic.sub.safe': lambda n, pre: refl(False_())}})\ndef bad(n: Nat) -> Nat:\n    return n - n\n");
    assert!(check_module(&source, Target::Python314).is_err());
    let source = format!("{HEADER}@verified\ndef hidden() -> Nat:\n    return 3\n@verified\ndef bad() -> Nat:\n    return hidden() - 1\n");
    assert!(check_module(&source, Target::Python314).is_err());
}

#[test]
fn signed_locals_work_in_loop_state_and_arithmetic_keeps_parallel_snapshots() {
    check(
        r#"
from deppy.integer import Int, Pos, Neg
@verified
def mixed(n: Nat) -> Int:
    k = n
    x: Int = -2
    while 0 < k:
        decreases(k)
        k -= 1
        x += 1
    return x
@verified
def parallel() -> Refined[Nat, lambda r: Eq[Nat, r, 6]]:
    x = 4
    y = 2
    x, y = x - y, x
    return x + y
@theorem
def computes_mixed() -> Eq[Int, mixed(3), Pos(1)]:
    return refl(Pos(1))
"#,
    );
}

#[test]
fn numeric_example_is_statically_checked() {
    check_module(
        include_str!("../examples/verified/verified_numeric.py"),
        Target::Python314,
    )
    .unwrap();
}

#[test]
fn imported_numeric_contracts_preserve_axiom_dependencies() {
    let library = format!("{HEADER}from deppy import axiom\n@axiom\ndef assumed(n: Nat) -> LE(n, n):\n    ...\n@verified(proofs={{'arithmetic.sub.safe': lambda n, pre: bound(n, n, assumed(n))}})\ndef zero(n: Nat) -> Nat:\n    return n - n\n").replace("from deppy import axiom\n", "from deppy import axiom\nfrom deppy.arithmetic import sub_bound as bound\n");
    let source = format!(
        "{HEADER}from facade import zero\n@verified\ndef use(n: Nat) -> Nat:\n    return zero(n)\n"
    );
    let checked =
        deppy_python::check_module_with_resolver(&source, Target::Python314, &mut |name: &str| {
            Ok(match name {
                "library" => Some(library.clone()),
                "facade" => Some("from library import zero\n".to_owned()),
                _ => None,
            })
        })
        .unwrap();
    assert_eq!(checked.axiom_dependencies["use"], vec!["library.assumed"]);
}

#[test]
fn signed_add_subtract_multiply_compare_and_guarded_conversion() {
    check(
        r#"
from deppy.integer import Int, Pos, Neg, of_nat, to_nat
@verified
def ops() -> Refined[Int, lambda r: Eq[Int, r, Neg(8)]]:
    x: Int = -2
    y: Int = 3
    assert x < y
    assert x <= -2
    assert y > x
    assert y >= 3
    assert x != y
    assert -0 == 0
    return (x + y) * (x - y - 4)
@verified
def equal(n: Int) -> Refined[Int, lambda r: Eq[Int, r, Pos(0)]]:
    if n == 0:
        return n
    return 0
@verified
def natural(n: Int) -> Nat:
    if n >= 0:
        return to_nat(n)
    return 0
"#,
    );
}

#[test]
fn contextual_integer_literals_survive_normalization_and_parallel_updates() {
    check(
        r#"
from deppy.integer import Int, Pos, Neg
@verified
def signed_literals() -> Refined[Int, lambda r: Eq[Int, r, Neg(0)]]:
    return 1 - 2
@verified
def nested_literals() -> Refined[Int, lambda r: Eq[Int, r, Neg(0)]]:
    x: Int = 8
    x = 1 + (2 - 4)
    x, y = 1 - 3, -1
    return x - y
@verified
def conditional(flag: Bool) -> Int:
    return 1 - 2 if flag else 0
"#,
    );
}

#[test]
fn numeric_inference_keeps_boolean_equality_and_nested_conditionals() {
    check(
        r#"
from deppy.integer import Int, Pos, Neg
@verified
def equality(b: Bool, n: Nat) -> Bool:
    x: Bool = (not b) == (not b)
    x = (n < n) == False
    x = (b and b) == b
    return (True if b else False) == b
@verified
def conditional_arithmetic(flag: Bool) -> Int:
    x = (-1 if flag else -2) + 1
    return x
"#,
    );
}

#[test]
fn operators_link_their_libraries_without_explicit_helper_imports() {
    let source = r#"
from __future__ import annotations
from deppy import Nat, Eq, refl, theorem
from deppy.verified import verified
@verified
def numeric() -> Nat:
    x = 5 - 2
    x //= 2
    return x
@verified
def negative_comparison() -> Nat:
    if -1 < 0:
        return 1
    return 0
@theorem
def result() -> Eq[Nat, numeric(), 1]:
    return refl(1)
@theorem
def negative_result() -> Eq[Nat, negative_comparison(), 1]:
    return refl(1)
"#;
    check_module(source, Target::Python314).unwrap();
}
