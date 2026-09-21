use deppy_python::{analyze_module, check_module, check_module_with_resolver, Target};
const TARGET: Target = Target::Python314;
const HEADER: &str = "from __future__ import annotations\nfrom deppy import Nat, Eq, refl, theorem, hole\nfrom deppy.data import Bool, True_, False_, Unit, MkUnit\nfrom deppy.verified import verified, Refined, verified_spec\nfrom deppy.verified_loop import decreases\nfrom deppy.nat_order import LE, LT\n";
const LOOP: &str = include_str!("../examples/verified_annotations.py");

#[test]
fn annotations_are_the_default_interface_and_plain_results_guarantee_only_the_base_type() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified
def identity(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    return n
@verified()
def keep(flag: Bool) -> Refined[Bool, lambda r: Eq[Bool, r, flag]]:
    return flag
@verified
def plain(n: Nat) -> Nat:
    return n + 1
@verified
def compose(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    value = identity(n)
    return value
@theorem
def spec(n: Nat) -> Eq[Nat, compose(n), n]:
    return verified_spec(compose, n, MkUnit())
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn countdown_infers_invariant_and_proves_contracts_and_totality_without_axioms() {
    let checked = check_module(LOOP, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let client = format!("{HEADER}from facade import count\n@theorem\ndef spec(n: Nat) -> Eq[Nat, count(n), 0]:\n    return verified_spec(count, n, MkUnit())\n@theorem\ndef computes() -> Eq[Nat, count(3), 0]:\n    return refl(0)\n");
    check_module_with_resolver(&client, TARGET, &mut |name: &str| {
        Ok(match name {
            "library" => Some(LOOP.into()),
            "facade" => Some("from library import bounded_countdown as count\n".into()),
            _ => None,
        })
    })
    .unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn false_contracts_and_non_decreasing_loops_leave_goals() {
    for (from, to) in [
        ("counter = decrement(counter)", "counter = counter"),
        ("counter = decrement(counter)", "counter = decrement(0)"),
        ("decreases(counter)", "decreases(0)"),
        ("return counter", "return n + 1"),
        ("LE[value, n]", "LT(value, n)"),
    ] {
        let source = LOOP.replace(from, to);
        let analysis = analyze_module(&source, TARGET);
        assert!(analysis.checked.is_none(), "{from} -> {to}");
        assert!(
            !analysis.goals.is_empty(),
            "{from} -> {to}: {:?}",
            analysis.diagnostics
        );
    }
}

#[test]
fn missing_evidence_is_a_located_goal_and_manual_mode_keeps_all_vcs() {
    let source = format!("{HEADER}@verified\ndef false_claim(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return n\n");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    let goal = &analysis.goals[0];
    assert_eq!(goal.name, "false_claim.return");
    let location = goal.location.as_ref().unwrap();
    assert_eq!(&source[location.start..location.end], "n");
    assert!(goal.context.iter().any(|c| c.name == "n"));
    let manual = LOOP.replace(
        "@verified\ndef bounded_countdown",
        "@verified(auto=False)\ndef bounded_countdown",
    );
    let analysis = analyze_module(&manual, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 12, "{:?}", analysis.diagnostics);
    for name in [
        "local.counter.refined",
        "loop.init",
        "loop.preserve",
        "loop.decrease",
        "loop.exit",
    ] {
        assert!(analysis
            .goals
            .iter()
            .any(|g| g.name == format!("bounded_countdown.{name}")));
    }
}

#[test]
fn explicit_proofs_and_holes_are_never_overridden_and_partial_maps_supplement_auto() {
    let source = format!("{HEADER}@verified\ndef identity(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    return n\n");
    let wrong = source.replace(
        "@verified\n",
        "@verified(proofs={'return': lambda n, pre: refl(0)})\n",
    );
    assert!(check_module(&wrong, TARGET).is_err());
    let hole = source.replace(
        "@verified\n",
        "@verified(proofs={'return': lambda n, pre: hole('manual')})\n",
    );
    assert_eq!(analyze_module(&hole, TARGET).goals[0].name, "manual");
    let supplemented = LOOP.replace("@verified\ndef bounded", "@verified(proofs={'local.counter.refined': lambda n, pre, value: le_refl(n)})\ndef bounded")
        .replace("from deppy.nat_order import LE, LT", "from deppy.nat_order import LE, LT, le_refl");
    check_module(&supplemented, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn sigma_preconditions_and_multiple_local_invariants_are_reused() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy.nat import pred_or
@verified
def decrement(n: Refined[Nat, lambda v: LT(0, v)]) -> Refined[Nat, lambda r: LT(r, n)]:
    return pred_or(0, n)
@verified
def keep(n: Refined[Nat, lambda v: Eq[Nat, v, 0]], flag: Refined[Bool, lambda v: Eq[Bool, v, True_()]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return n
@verified
def zero(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x: Refined[Nat, lambda v: Eq[Nat, v, 0]] = 0
    y: Refined[Nat, lambda v: LE[v, n]] = n
    while 0 < y:
        decreases(y)
        x = x
        y = decrement(y)
    return x
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(&source.replace("x = x", "x = n"), TARGET).is_err());
}

#[test]
fn guard_evidence_is_path_specific() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified
def positive(n: Refined[Nat, lambda v: LT(0, v)]) -> Refined[Nat, lambda r: LT(0, r)]:
    return n
@verified
def choose(n: Nat) -> Nat:
    if 0 < n:
        return positive(n)
    return 0
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    let wrong = source.replace("    return 0", "    return positive(n)");
    let analysis = analyze_module(&wrong, TARGET);
    assert!(analysis.checked.is_none());
    assert!(analysis
        .goals
        .iter()
        .any(|g| g.name == "choose.else.call.return.requires"));
}

#[test]
fn auto_uses_abstract_contracts_and_preserves_axiom_dependencies() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy import axiom
@axiom
def assumed(n: Nat) -> Eq[Nat, n, 0]:
    ...
@verified(proof=lambda n, pre: assumed(n))
def trusted(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return n
@verified
def client(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = trusted(n)
    return x
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(checked.axiom_dependencies["client"], vec!["assumed"]);
    // A user axiom is not an automatic hint merely because it is in scope.
    assert!(check_module(&source.replace("    x = trusted(n)", "    x = n"), TARGET).is_err());
    let abstracted = format!("{HEADER}@verified\ndef identity(n: Nat) -> Nat:\n    return n\n@verified\ndef client(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    x = identity(n)\n    return x\n");
    let analysis = analyze_module(&abstracted, TARGET);
    assert!(analysis.checked.is_none());
    assert!(analysis.goals.iter().any(|g| g.name == "client.return"));
}

#[test]
fn inferred_state_requires_initialization_and_keeps_annotation_snapshots() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified
def capture(n: Nat) -> Refined[Nat, lambda r: LE[r, n]]:
    bound = n
    x: Refined[Nat, lambda v: LE[v, bound]] = n
    bound = n + 1
    x = x
    return x
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(&source.replace("x = x", "x = bound"), TARGET).is_err());
    let uninitialized = LOOP.replace(
        "        counter = decrement(counter)",
        "        other = counter\n        counter = decrement(counter)",
    );
    assert!(check_module(&uninitialized, TARGET).is_err());
    let explicit = LOOP.replace("from deppy.verified_loop import decreases", "from deppy.verified_loop import invariant, decreases")
        .replace("        decreases(counter)", "        invariant(lambda counter: LE[counter, n], state=(counter,))\n        decreases(counter)");
    check_module(&explicit, TARGET).unwrap_or_else(|e| panic!("{e}"));
}
