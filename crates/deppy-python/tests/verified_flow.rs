use deppy_python::{analyze_module, check_module, Target};
const HEADER: &str = "from deppy import Nat, Eq, refl, theorem\nfrom deppy.data import Bool, True_, False_\nfrom deppy.verified import verified, Refined\nfrom deppy.nat import pred_or\nfrom deppy.verified_loop import decreases, invariant\n";
fn check(body: &str) {
    let source = format!("{HEADER}{body}");
    let checked =
        check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}\n{source}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}
const SEQUENTIAL: &str = r#"
@verified
def sequential(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n
    while 0 < x:
        decreases(x)
        x = pred_or(0, x)
    y = x
    while 0 < y:
        invariant(lambda y: Eq[Nat, y, 0], state=(y,))
        decreases(y)
        y = 0
    return y
@theorem
def computes() -> Eq[Nat, sequential(3), 0]:
    return refl(0)
"#;
#[test]
fn sequential_loops_pass_exit_evidence_to_initialization() {
    check(SEQUENTIAL);
}
#[test]
fn loops_in_branches_and_branch_initialization() {
    check(
        r#"
@verified
def branches(flag: Bool, n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n if flag else 0
    if flag:
        while 0 < x:
            decreases(x)
            x = pred_or(0, x)
    else:
        while 0 < x:
            decreases(x)
            x = pred_or(0, x)
    return x
@theorem
def computes_true() -> Eq[Nat, branches(True_(), 3), 0]:
    return refl(0)
@theorem
def computes_false() -> Eq[Nat, branches(False_(), 3), 0]:
    return refl(0)
"#,
    );
}
#[test]
fn nested_loops_use_inner_exit_and_termination() {
    check(
        r#"
@verified
def nested(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = x
        while 0 < y:
            decreases(y)
            y = pred_or(0, y)
        x = pred_or(0, x)
    return x
@theorem
def computes() -> Eq[Nat, nested(3), 0]:
    return refl(0)
"#,
    );
}
#[test]
fn bad_loop_updates_and_uninitialized_state_are_rejected() {
    for (from, to) in [
        ("x = pred_or(0, x)", "x = x"),
        ("y = x", "y = 1"),
        ("y = 0", "y = 1"),
        ("decreases(x)", "decreases(0)"),
        ("while 0 < y:", "while 0 <= y:"),
    ] {
        assert!(
            check_module(
                &format!("{HEADER}{}", SEQUENTIAL.replace(from, to)),
                Target::Python314
            )
            .is_err(),
            "{from} -> {to}"
        );
    }
}
#[test]
fn loops_have_distinct_goals_and_source_locations() {
    let source = format!(
        "{HEADER}{}",
        SEQUENTIAL.replace("@verified", "@verified(auto=False)")
    );
    let analysis = analyze_module(&source, Target::Python314);
    assert!(analysis.checked.is_none());
    assert!(
        analysis
            .goals
            .iter()
            .any(|g| g.name == "sequential.loop.1.init"),
        "{:?}",
        analysis.diagnostics
    );
    assert!(analysis
        .goals
        .iter()
        .any(|g| g.name == "sequential.loop.1.exit.loop.2.init"));
    assert!(analysis.goals.iter().all(|g| g.location.is_some()));
}

#[test]
fn continue_checks_decrease_and_skips_the_remaining_body() {
    check(
        r#"
@verified
def continued(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n
    while 0 < x:
        decreases(x)
        x = pred_or(0, x)
        continue
        assert False
    return x
@theorem
def computes() -> Eq[Nat, continued(4), 0]:
    return refl(0)
"#,
    );
    let body = r#"
@verified
def bad(n: Nat) -> Nat:
    x = n
    while 0 < x:
        decreases(x)
        if 0 < x:
            continue
        x = pred_or(0, x)
    return x
"#;
    assert!(check_module(&format!("{HEADER}{body}"), Target::Python314).is_err());
}

#[test]
fn inner_continue_targets_the_inner_loop_only() {
    check(
        r#"
@verified
def nested(n: Nat) -> Nat:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = x
        while 0 < y:
            decreases(y)
            y = pred_or(0, y)
            continue
        x = pred_or(0, x)
    return x
@theorem
def computes() -> Eq[Nat, nested(3), 0]:
    return refl(0)
"#,
    );
}

#[test]
fn nested_loop_state_is_initialized_and_declared_in_outer_loop() {
    let body = r#"
@verified
def bad(n: Nat) -> Nat:
    x = n
    y = n
    while 0 < x:
        invariant(lambda x: Eq[Nat, x, n], state=(x,))
        decreases(x)
        while 0 < y:
            decreases(y)
            y = pred_or(0, y)
        x = pred_or(0, x)
    return x
"#;
    let err = check_module(&format!("{HEADER}{body}"), Target::Python314)
        .err()
        .unwrap();
    assert!(err.to_string().contains("declared state variable"), "{err}");
    let err = check_module(
        &format!(
            "{HEADER}{}",
            body.replace("    y = n\n", "").replace(
                "        invariant(lambda x: Eq[Nat, x, n], state=(x,))\n",
                ""
            )
        ),
        Target::Python314,
    )
    .err()
    .unwrap();
    assert!(err.to_string().contains("initialized"), "{err}");
}

#[test]
fn body_contracts_are_checked_once_and_keep_their_source_range() {
    let body = r#"
@verified
def identity(n: Nat) -> Nat:
    return n
@verified(auto=False)
def caller(n: Nat) -> Nat:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = identity(x)
        x = pred_or(0, x)
        continue
    return x
"#;
    let source = format!("{HEADER}{body}");
    let analysis = analyze_module(&source, Target::Python314);
    let calls = analysis
        .goals
        .iter()
        .filter(|g| g.name.contains("call.y.requires"))
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1, "{:?}", analysis.diagnostics);
    assert_eq!(calls[0].name, "caller.loop.1.step.call.y.requires");
    let location = calls[0].location.as_ref().unwrap();
    assert_eq!(&source[location.start..location.end], "identity(x)");
}

#[test]
fn nested_contract_results_cannot_bypass_their_specification() {
    let body = r#"
@verified
def unknown() -> Nat:
    return 0
@verified
def caller(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = unknown()
        while 0 < y:
            invariant(lambda y: Eq[Nat, y, 0], state=(y,))
            decreases(y)
            y = 0
        x = pred_or(0, x)
    return x
"#;
    let analysis = analyze_module(&format!("{HEADER}{body}"), Target::Python314);
    assert!(analysis.checked.is_none());
    assert!(
        analysis
            .goals
            .iter()
            .any(|g| g.name.ends_with("loop.2.init")),
        "{:?}",
        analysis.diagnostics
    );
}

#[test]
fn explicit_flow_proofs_override_automatic_search() {
    let wrong = SEQUENTIAL.replace(
        "@verified",
        "@verified(proofs={'loop.1.init': lambda n, pre: refl(0)})",
    );
    assert!(check_module(&format!("{HEADER}{wrong}"), Target::Python314).is_err());
}

#[test]
fn reexported_contracts_in_composed_loops_keep_axiom_dependencies() {
    use deppy_python::check_module_with_resolver;
    let library = format!("{HEADER}from deppy import axiom\n@axiom\ndef assumed() -> Eq[Nat, 0, 0]:\n    ...\n@verified(proof=lambda pre: assumed())\ndef zero() -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return 0\n");
    let caller = format!("{HEADER}from facade import zero\n@verified\ndef caller(n: Nat) -> Nat:\n    x = n\n    y = 0\n    while 0 < x:\n        decreases(x)\n        y = zero()\n        x = pred_or(0, x)\n        continue\n    return x\n");
    let checked = check_module_with_resolver(&caller, Target::Python314, &mut |name: &str| {
        Ok(match name {
            "library" => Some(library.clone()),
            "facade" => Some("from library import zero\n".into()),
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
fn contract_initialization_after_a_branch_uses_path_evidence() {
    check(
        r#"
@verified
def zero(n: Refined[Nat, lambda n: Eq[Nat, n, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return n
@verified
def initialized(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    if n == 0:
        x = zero(n)
    else:
        x = n
    while 0 < x:
        decreases(x)
        x = pred_or(0, x)
    return x
@theorem
def computes() -> Eq[Nat, initialized(3), 0]:
    return refl(0)
"#,
    );
}
