use deppy_python::{analyze_module, check_module, check_module_with_resolver, Target};
const HEADER: &str = "from deppy import Nat, Eq, refl, theorem\nfrom deppy.data import Bool, True_, False_, MkUnit\nfrom deppy.verified import verified, Refined, nat_lt\nfrom deppy.nat import pred_or\nfrom deppy.nat_order import LT\nfrom deppy.verified_loop import decreases\n";
const LIB: &str = "@verified\ndef zero(n: Refined[Nat, lambda n: Eq[Nat, n, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return n\n";
fn check(body: &str) {
    let source = format!("{HEADER}{LIB}{body}");
    let checked =
        check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}\n{source}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}
#[test]
fn nested_calls_arithmetic_and_parallel_assignments() {
    check(
        r#"
@verified
def nested() -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return zero(zero(0))
@verified
def arithmetic() -> Nat:
    return zero(0) + zero(0) + 1
@verified
def swap() -> Nat:
    x = 0
    y = 2
    x, y = y, zero(x)
    return x + y
@theorem
def result() -> Eq[Nat, swap(), 2]:
    return refl(2)
"#,
    );
    assert!(check_module(
        &format!("{HEADER}{LIB}@verified\ndef bad() -> Nat:\n    return zero(1) + 1\n"),
        Target::Python314
    )
    .is_err());
}
#[test]
fn boolean_operators_conditionals_assert_and_augassign() {
    check(
        r#"
@verified
def expressions() -> Nat:
    x = 0
    x += 1
    assert x == 1
    assert x != 0
    assert x > 0
    assert x >= 1
    assert not False
    assert True == True
    assert True != False
    assert True and (False or True)
    y = zero(0) if True else 1
    return x + y
@theorem
def computes() -> Eq[Nat, expressions(), 1]:
    return refl(1)
"#,
    );
    for expression in [
        "False",
        "0",
        "1 == True",
        "1 and True",
        "not 1",
        "True > False",
    ] {
        let source = format!(
            "{HEADER}@verified\ndef bad() -> Nat:\n    assert {expression}\n    return 0\n"
        );
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{expression}"
        );
    }
}
#[test]
fn branch_evidence_reaches_conditional_calls_and_assert_continuations() {
    check(
        r#"
@verified
def positive(n: Refined[Nat, lambda n: LT(0, n)]) -> Bool:
    return True
@verified
def use(n: Nat) -> Bool:
    return positive(n) if 0 < n else False
@verified
def conjunction(n: Nat) -> Bool:
    return 0 < n and positive(n)
@verified
def disjunction(n: Nat) -> Bool:
    return not (0 < n) or positive(n)
@verified
def asserted(n: Refined[Nat, lambda n: Eq[Bool, nat_lt(0, n), True_()]]) -> Bool:
    assert 0 < n
    return positive(n)
"#,
    );
}
#[test]
fn generated_call_goals_have_distinct_names_and_original_ranges() {
    let source = format!(
        "{HEADER}{LIB}@verified(auto=False)\ndef goals() -> Nat:\n    return zero(0) + zero(0)\n"
    );
    let result = analyze_module(&source, Target::Python314);
    assert!(result.checked.is_none());
    assert_eq!(result.goals.len(), 3, "{:?}", result.diagnostics);
    assert_ne!(result.goals[0].name, result.goals[1].name);
    for goal in &result.goals[..2] {
        let span = goal.location.as_ref().unwrap();
        assert_eq!(&source[span.start..span.end], "zero(0)");
    }
    assert!(
        result.goals[0].location.as_ref().unwrap().start
            < result.goals[1].location.as_ref().unwrap().start
    );
}
#[test]
fn contract_calls_initialize_loop_state() {
    check(
        r#"
@verified
def initialize() -> Nat:
    x = zero(zero(0)) + 1
    while 0 < x:
        decreases(x)
        x = pred_or(0, x)
    return x
@theorem
def computes() -> Eq[Nat, initialize(), 0]:
    return refl(0)
"#,
    );
}
#[test]
fn imported_contracts_are_checked_inside_expressions() {
    let library = format!("{HEADER}{LIB}");
    let source = format!("{HEADER}from facade import step\n@verified\ndef use() -> Nat:\n    return step(step(0)) + 1\n");
    let mut resolver = |name: &str| {
        Ok(match name {
            "library" => Some(library.clone()),
            "facade" => Some("from library import zero as step\n".into()),
            _ => None,
        })
    };
    check_module_with_resolver(&source, Target::Python314, &mut resolver).unwrap();
    assert!(check_module_with_resolver(
        &source.replace("step(0)", "step(1)"),
        Target::Python314,
        &mut resolver
    )
    .is_err());
}

#[test]
fn contracts_stay_abstract_and_explicit_proofs_take_precedence() {
    let source = format!("{HEADER}@verified\ndef opaque_value() -> Nat:\n    return 0\n@verified\ndef bad() -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return opaque_value() + 0\n");
    assert!(check_module(&source, Target::Python314).is_err());
    let source = format!("{HEADER}{LIB}@verified\ndef bad() -> Nat:\n    return zero(0) + 1\n");
    let manual = source.replace("@verified\ndef bad", "@verified(auto=False)\ndef bad");
    let analysis = analyze_module(&manual, Target::Python314);
    let key = analysis.goals[0].name.strip_prefix("bad.").unwrap();
    let wrong = source.replace(
        "@verified\ndef bad",
        &format!("@verified(proofs={{'{key}': lambda pre: refl(1)}})\ndef bad"),
    );
    assert!(check_module(&wrong, Target::Python314).is_err());
}

#[test]
fn short_circuit_and_elif_only_require_reachable_preconditions() {
    check(
        r#"
@verified
def checked(n: Refined[Nat, lambda n: Eq[Nat, n, 0]]) -> Bool:
    return True
@verified
def skip() -> Bool:
    if False and checked(1):
        return False
    elif True or checked(1):
        return checked(0)
    return False
"#,
    );
    for expression in [
        "True and checked(1)",
        "False or checked(1)",
        "checked(1) if True else False",
    ] {
        let source = format!("{HEADER}@verified\ndef checked(n: Refined[Nat, lambda n: Eq[Nat, n, 0]]) -> Bool:\n    return True\n@verified\ndef bad() -> Bool:\n    return {expression}\n");
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{expression}"
        );
    }
}

#[test]
fn nested_calls_inside_loop_transitions_preserve_state_and_contracts() {
    check(
        r#"
@verified
def keep(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    return n
@verified
def loop(n: Nat) -> Nat:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        x, y = pred_or(0, x), zero(zero(0))
    return keep(keep(x))
"#,
    );
}

#[test]
fn nested_contracts_keep_axiom_dependencies() {
    let source = format!("{HEADER}from library import trusted_zero\n@verified\ndef caller() -> Nat:\n    return trusted_zero() + 1\n");
    let library = format!("{HEADER}from deppy import axiom\n@axiom\ndef assumed() -> Eq[Nat, 0, 0]:\n    ...\n@verified(proof=lambda pre: assumed())\ndef trusted_zero() -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return 0\n");
    let checked = check_module_with_resolver(&source, Target::Python314, &mut |_: &str| {
        Ok(Some(library.clone()))
    })
    .unwrap();
    assert!(checked.axiom_dependencies["caller"]
        .iter()
        .any(|name| name.contains("assumed")));
}

#[test]
fn equality_guards_and_assertions_supply_checked_evidence() {
    check(
        r#"
@verified
def equal(n: Nat) -> Nat:
    if n == 0:
        return zero(n)
    return n
@verified
def assertion_before_loop(n: Nat) -> Nat:
    assert n <= n
    x = n
    while 0 < x:
        decreases(x)
        assert x <= x
        x = pred_or(0, x)
    return x
"#,
    );
    let source = format!("{HEADER}@verified\ndef unknown() -> Nat:\n    return 0\n@verified\ndef bad() -> Nat:\n    x: Refined[Nat, lambda x: Eq[Nat, x, 0]] = unknown()\n    while 0 < x:\n        decreases(x)\n        x = pred_or(0, x)\n    return x\n");
    assert!(check_module(&source, Target::Python314).is_err());
}

#[test]
fn parallel_pure_bool_calls_keep_the_target_type() {
    check(
        r#"
@theorem
def flag() -> Bool:
    return True_()
@verified
def use(b: Bool, n: Nat) -> Bool:
    b, n = flag(), zero(0)
    return b
"#,
    );
}
