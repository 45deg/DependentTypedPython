use deppy_python::{analyze_module, check_module, Target};
const HEADER: &str = "from deppy import Nat, Eq, refl, theorem\nfrom deppy.data import Bool, True_, False_\nfrom deppy.verified import verified, Refined, nat_lt\nfrom deppy.nat_order import LT\nfrom deppy.nat import pred_or\nfrom deppy.verified_loop import invariant, decreases\n";
fn check(body: &str) {
    check_budget(body, 1_000_000, false);
}
fn check_budget(body: &str, budget: usize, large_stack: bool) {
    let source = format!("{HEADER}{body}");
    let run = move || {
        let checked = deppy_python::check_module_with_options(
            &source,
            deppy_python::FrontendOptions {
                target: Target::Python314,
                elaboration_steps: budget,
                ..Default::default()
            },
        )
        .unwrap_or_else(|e| panic!("{e}\n{source}"));
        assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    };
    // The nested range certificate now fits the default step budget, but
    // recursive checking still needs the existing large-proof worker stack.
    if large_stack {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(run)
            .unwrap()
            .join()
            .unwrap();
    } else {
        run();
    }
}
#[test]
fn break_is_an_early_exit_even_at_measure_zero() {
    check(
        r#"
@verified
def early() -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:
    x = 0
    while True:
        invariant(lambda x: Eq[Nat, x, 0], state=(x,))
        decreases(0)
        x = 7
        break
        assert False
    return x
@theorem
def computes() -> Eq[Nat, early(), 7]:
    return refl(7)
"#,
    );
}
#[test]
fn return_exits_all_nested_loops() {
    check(
        r#"
@verified
def early(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = x
        while 0 < y:
            decreases(y)
            return 7
        x = pred_or(0, x)
    return 7
@theorem
def computes() -> Eq[Nat, early(3), 7]:
    return refl(7)
"#,
    );
}
#[test]
fn break_does_not_supply_false_guard_evidence() {
    let source = format!("{HEADER}@verified\ndef bad(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    x = n\n    while 0 < x:\n        decreases(x)\n        break\n    return x\n");
    let analysis = analyze_module(&source, Target::Python314);
    assert!(analysis.checked.is_none());
    assert!(
        analysis
            .goals
            .iter()
            .any(|g| g.name.contains("break.return")),
        "{:?}",
        analysis.diagnostics
    );
}
#[test]
fn return_from_one_loop() {
    check(
        r#"
@verified
def one(n: Nat) -> Nat:
    x = n
    while 0 < x:
        decreases(x)
        return 7
    return 0
@theorem
def computes() -> Eq[Nat, one(3), 7]:
    return refl(7)
"#,
    );
}
#[test]
fn range_order_empty_and_body_target_updates() {
    check(
        r#"
@verified
def ascending(stop: Nat) -> Nat:
    i = 9
    acc = 0
    for i in range(1, stop, 2):
        acc = acc * 2 + i
        i = 8
    return acc
@verified
def descending(start: Nat) -> Nat:
    i = 9
    acc = 0
    for i in range(start, 0, -2):
        acc = acc * 2 + i
    return acc
@verified
def empty() -> Nat:
    i = 9
    for i in range(3, 1):
        i = 0
    return i
@theorem
def computes_up() -> Eq[Nat, ascending(6), 15]:
    return refl(15)
@theorem
def computes_down() -> Eq[Nat, descending(5), 27]:
    return refl(27)
@theorem
def computes_empty() -> Eq[Nat, empty(), 9]:
    return refl(9)
"#,
    );
}

#[test]
fn range_continue_break_and_return_have_distinct_destinations() {
    check(
        r#"
@verified
def skip(stop: Nat) -> Nat:
    i = 0
    acc = 0
    for i in range(stop):
        acc += 1
        continue
        assert False
    return acc
@verified
def stop_early(stop: Nat) -> Nat:
    i = 9
    for i in range(stop):
        break
    return i
@verified
def returned(stop: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:
    i = 0
    for i in range(stop):
        return 7
    return 7
@theorem
def skipped() -> Eq[Nat, skip(3), 3]:
    return refl(3)
@theorem
def stopped() -> Eq[Nat, stop_early(3), 0]:
    return refl(0)
@theorem
def result() -> Eq[Nat, returned(3), 7]:
    return refl(7)
"#,
    );
}

#[test]
fn range_boundaries_are_snapshots_and_nested_cursors_are_private() {
    check_budget(
        r#"
@verified
def snapshots(n: Nat) -> Nat:
    i = 0
    acc = 0
    for i in range(n):
        n = 0
        acc += 1
    return acc
@verified
def nested(n: Nat) -> Nat:
    i = 0
    j = 0
    acc = 0
    for i in range(n):
        for j in range(n):
            acc += 1
            break
    return acc
@theorem
def snapshot_result() -> Eq[Nat, snapshots(3), 3]:
    return refl(3)
@theorem
def nested_result() -> Eq[Nat, nested(2), 2]:
    return refl(2)
"#,
        1_000_000,
        true,
    );
}

#[test]
fn zero_stride_bad_types_shadowing_and_wrong_returns_are_rejected() {
    for statement in [
        "for i in range(n, n, 0):",
        "for i in range(n, n, -0):",
        "for i in range(n, n, False):",
        "for i in range(n, n, -n):",
        "for i in range(-1):",
    ] {
        let source = format!("{HEADER}@verified\ndef bad(n: Nat) -> Nat:\n    i = 0\n    {statement}\n        i = 0\n    return i\n");
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{statement}"
        );
    }
    for body in [
        "    i = 0\n    range = 0\n    for i in range(n):\n        i = 0\n    return i\n",
        "    for i in range(n):\n        i = 0\n    return i\n",
        "    x = n\n    while 0 < x:\n        decreases(x)\n        return 1\n    return 0\n",
    ] {
        let source = format!(
            "{HEADER}@verified\ndef bad(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n{body}"
        );
        assert!(check_module(&source, Target::Python314).is_err(), "{body}");
    }
}

#[test]
fn many_normal_branches_share_the_continuation_within_the_default_budget() {
    let mut body = "@verified\ndef branches(flag: Bool) -> Nat:\n    x = 0\n".to_string();
    for _ in 0..8 {
        body.push_str("    if flag:\n        x += 1\n    else:\n        x += 2\n");
    }
    body.push_str("    return x\n");
    check(&body);
}

#[test]
fn shared_continuations_keep_branch_specific_contract_evidence() {
    check(
        r#"
@verified
def zero(n: Refined[Nat, lambda n: Eq[Nat, n, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return n
@verified
def use(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    if n == 0:
        x = zero(n)
    else:
        x = zero(0)
    return zero(x)
"#,
    );
}

#[test]
fn range_stride_and_iteration_bounds_have_checked_evidence() {
    check(
        r#"
@verified
def bounded(stop: Nat, stride: Refined[Nat, lambda s: LT(0, s)]) -> Nat:
    i = 0
    for i in range(0, stop, stride):
        assert i < stop
    return i
"#,
    );
}

#[test]
fn range_links_its_checked_interpreter_without_a_directive_import() {
    let source = "from deppy import Nat\nfrom deppy.verified import verified\n@verified\ndef count(n: Nat) -> Nat:\n    i = 0\n    total = 0\n    for i in range(n):\n        total += 1\n    return total\n";
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn range_step_goal_has_the_original_argument_location() {
    let source = format!("{HEADER}@verified\ndef use(n: Nat, stride: Nat) -> Nat:\n    i = 0\n    for i in range(0, n, stride):\n        i = i\n    return i\n");
    let analysis = analyze_module(&source, Target::Python314);
    let goal = analysis
        .goals
        .iter()
        .find(|g| g.name == "use.range.step.positive")
        .unwrap_or_else(|| panic!("{:?}", analysis.diagnostics));
    let location = goal.location.as_ref().unwrap();
    assert_eq!(&source[location.start..location.end], "stride");
    assert!(analysis.checked.is_none());
}

#[test]
fn early_contract_returns_keep_imported_axiom_dependencies() {
    use deppy_python::check_module_with_resolver;
    let library = format!("{HEADER}from deppy import axiom\n@axiom\ndef assumed() -> Eq[Nat, 7, 7]:\n    ...\n@verified(proof=lambda pre: assumed())\ndef trusted() -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:\n    return 7\n");
    let caller = format!("{HEADER}from facade import trusted\n@verified\ndef caller(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:\n    while 0 < n:\n        decreases(0)\n        return trusted()\n    return 7\n");
    let checked = check_module_with_resolver(&caller, Target::Python314, &mut |name: &str| {
        Ok(match name {
            "library" => Some(library.clone()),
            "facade" => Some("from library import trusted\n".into()),
            _ => None,
        })
    })
    .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        checked.axiom_dependencies["caller"],
        vec!["library.assumed"]
    );
}

#[test]
fn explicit_early_return_proofs_are_not_replaced_by_automation() {
    let source = format!("{HEADER}@verified(proofs={{'loop.1.step.return': lambda n, pre, state, inv, test: refl(0)}})\ndef bad(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 7]]:\n    while 0 < n:\n        decreases(0)\n        return 7\n    return 7\n");
    assert!(check_module(&source, Target::Python314).is_err());
}
