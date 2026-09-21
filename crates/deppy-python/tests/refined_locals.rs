use deppy_python::{analyze_module, check_module, check_module_with_resolver, Target};
const TARGET: Target = Target::Python314;
const LOOP: &str = include_str!("../examples/refined_loop.py");
const HEADER: &str = "from __future__ import annotations\nfrom deppy import theorem, Nat, Eq, refl, S\nfrom deppy.data import Bool, True_, Unit, MkUnit\nfrom deppy.verified import verified, Refined, verified_spec\nfrom deppy.tactics import exact, rewrite\nfrom deppy.nat_order import LE, le_refl\n";

#[test]
fn loop_uses_only_contracts_and_exports_a_checked_specification() {
    let checked = check_module(LOOP, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let client = format!("{HEADER}from library import bounded_countdown as count\n@theorem\ndef correct(n: Nat) -> Eq[Nat, count(n), 0]:\n    return verified_spec(count, n, MkUnit())\n");
    let checked = check_module_with_resolver(&client, TARGET, &mut |name: &str| {
        Ok((name == "library").then(|| LOOP.to_owned()))
    })
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies["correct"].is_empty());
    for (from, to) in [
        ("return pred_or(0, n)", "return n"),
        ("LT(result, n)", "LT(result, 0)"),
        ("counter = decrement(counter)", "counter = decrement(0)"),
        (
            "counter = decrement(counter)",
            "counter = S(decrement(counter))",
        ),
        (
            "counter = decrement(counter)",
            "counter, other = decrement(counter), counter",
        ),
        ("counter = decrement(counter)", "counter = counter"),
        (
            "invariant(lambda counter: LE[counter, n]",
            "invariant(lambda counter: LE[counter, 0]",
        ),
        (
            "decreases(lambda counter: counter)",
            "decreases(lambda counter: 0)",
        ),
        (
            "exact(smaller)",
            "pred_lt(state.fst, decision_true(lt_decide(0, state.fst), test))",
        ),
    ] {
        assert!(
            check_module(&LOOP.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}

#[test]
fn missing_loop_call_and_local_proofs_have_location_and_context() {
    for key in [
        "local.counter.refined",
        "loop.preserve.call.counter.requires",
        "loop.preserve.local.counter.refined",
        "loop.decrease.entry.local.counter.refined",
    ] {
        let source = LOOP
            .lines()
            .filter(|line| !line.contains(&format!("\"{key}\":")))
            .collect::<Vec<_>>()
            .join("\n");
        let analysis = analyze_module(&source, TARGET);
        assert!(analysis.checked.is_none());
        let goal = analysis
            .goals
            .iter()
            .find(|g| g.name == format!("bounded_countdown.{key}"))
            .unwrap_or_else(|| panic!("{key}: {:?}", analysis.diagnostics));
        let location = goal.location.as_ref().unwrap();
        assert!(location.end > location.start);
        assert!(goal.context.iter().any(|c| c.name == "n"));
        if key.contains("loop.") {
            assert!(goal.context.iter().any(|c| c.name == "$invariant"));
        }
    }
}

const LOCALS: &str = r#"
@verified(proofs={
    'local.x.refined': lambda n, pre, x: exact(pre),
    'local.y.refined': lambda n, pre, x, x_zero, y: rewrite(x_zero, le_refl(0)),
    'local.x.2.refined': lambda n, pre, x, x_zero, y, y_bound, new_x: refl(0),
    'local.y.2.refined': lambda n, pre, x, x_zero, y, y_bound, new_x, new_x_zero, new_y: le_refl(0),
    'return': lambda n, pre, x, x_zero, y, y_bound, new_x, new_x_zero, new_y, new_y_bound: exact(new_x_zero),
})
def convert(n: Refined[Nat, lambda v: Eq[Nat, v, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x: Refined[Nat, lambda v: Eq[Nat, v, 0]] = n
    y: Refined[Nat, lambda v: LE[v, 0]] = x
    x, y = 0, 0
    return x
"#;

#[test]
fn same_base_conversion_and_parallel_reassignment_are_checked() {
    let source = format!("{HEADER}{LOCALS}");
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    for changed in [
        source.replace("x, y = 0, 0", "x, y = 1, 0"),
        source.replace("x, y = 0, 0", "x, y = 0, 1"),
        source.replace("rewrite(x_zero, le_refl(0))", "refl(0)"),
        source.replace(
            "Refined[Nat, lambda v: LE[v, 0]] = x",
            "Refined[Bool, lambda v: Eq[Bool, v, True_()]] = x",
        ),
    ] {
        assert!(check_module(&changed, TARGET).is_err());
    }
}

#[test]
fn local_predicates_capture_annotation_environment_and_bool_is_supported() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(proofs={
    'local.x.refined': lambda n, pre, x: refl(n),
    'local.x.2.refined': lambda n, pre, x, fact, next_x: fact,
    'local.flag.refined': lambda n, pre, x, fact, next_x, next_fact, flag: refl(True_()),
    'return': lambda n, pre, x, fact, next_x, next_fact, flag, truth: exact(next_fact),
})
def capture(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    bound = n
    x: Refined[Nat, lambda v: Eq[Nat, v, bound]] = n
    bound = S(n)
    x = x
    flag: Refined[Bool, lambda v: Eq[Bool, v, True_()]] = True
    return x
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(&source.replace("    x = x", "    x = bound"), TARGET).is_err());
    assert!(check_module(&source.replace(" = True", " = False"), TARGET).is_err());
}

#[test]
fn refined_values_flow_into_contracts_and_conditions_cannot_be_forgotten() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(proof=lambda n, bound: bound)
def bounded(n: Refined[Nat, lambda v: LE[v, 0]]) -> Refined[Nat, lambda r: LE[r, 0]]:
    return n
@verified(proofs={
    'local.x.refined': lambda n, pre, x: pre,
    'call.y.requires': lambda n, pre, x, zero: rewrite(zero, le_refl(0)),
    'local.y.refined': lambda n, pre, x, zero, y, bound: exact(bound),
    'local.y.2.refined': lambda n, pre, x, zero, y, bound, local_bound, next_y: local_bound,
    'return': lambda n, pre, x, zero, y, bound, local_bound, next_y, next_bound: next_bound,
})
def convert_call(n: Refined[Nat, lambda v: Eq[Nat, v, 0]]) -> Refined[Nat, lambda r: LE[r, 0]]:
    x: Refined[Nat, lambda v: Eq[Nat, v, 0]] = n
    y: Refined[Nat, lambda v: LE[v, 0]] = bounded(x)
    y = y
    return y
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    for changed in [
        source.replace(" = n\n    y:", " = 1\n    y:"),
        source.replace("    y = y", "    y = 1"),
        source.replace("    y = y", "    y: Nat = 1"),
        source.replace("    y = y", "    y: Refined[Nat, lambda v: Unit] = 1"),
        source.replace("bounded(x)", "bounded(1)"),
    ] {
        assert!(check_module(&changed, TARGET).is_err());
    }
    let unmaintained = LOOP
        .replace(
            "invariant(lambda counter: LE[counter, n]",
            "invariant(lambda counter: Unit",
        )
        .replace(
            "from deppy.data import Bool,",
            "from deppy.data import Unit, Bool,",
        )
        .replace("initial_bound: initial_bound", "initial_bound: MkUnit()");
    assert!(check_module(&unmaintained, TARGET).is_err());
}

#[test]
fn branching_loop_contracts_use_guard_context_and_abstract_state_results() {
    let library = LOOP.split("@verified(proofs={").next().unwrap().replace(
        "from deppy.data import Bool,",
        "from deppy.data import Unit, Bool,",
    );
    let mut proofs = String::from("'loop.init': lambda n, pre: MkUnit(),\n'loop.exit': lambda n, pre, state, inv, test: stopped(state.fst, test),\n");
    for phase in ["preserve", "decrease"] {
        for branch in ["then", "else"] {
            proofs += &format!("'loop.{phase}.{branch}.call.x.requires': lambda n, pre, state, inv, test, branch: decision_true(lt_decide(0, state.fst), test),\n");
            proofs += &format!("'loop.{phase}.{branch}': lambda n, pre, state, inv, test, branch, value, smaller: {},\n", if phase == "preserve" { "MkUnit()" } else { "exact(smaller)" });
        }
    }
    let source = format!("{library}\n@verified(proofs={{{proofs}}})\ndef branched(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    x = n\n    while 0 < x:\n        invariant(lambda x: Unit, state=(x,))\n        decreases(lambda x: x)\n        if 0 < x:\n            x = decrement(x)\n        else:\n            x = decrement(x)\n    return x\n");
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace("x = decrement(x)", "x = decrement(0)"),
        TARGET
    )
    .is_err());
}

#[test]
fn imported_example_proof_reuses_loop_specification() {
    let source = include_str!("../examples/refined_loop_client.py");
    let checked = check_module_with_resolver(source, TARGET, &mut |name: &str| {
        Ok((name == "refined_loop").then(|| LOOP.to_owned()))
    })
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies["countdown_correct"].is_empty());
}

#[test]
fn exit_contracts_and_refined_locals_require_the_exit_evidence() {
    let helper = "@verified(proof=lambda n, pre: pre)\ndef keep_zero(n: Refined[Nat, lambda v: Eq[Nat, v, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return n\n\n";
    let source = LOOP.replace("@verified(proofs={", &format!("{helper}@verified(proofs={{"))
        .replace("    \"loop.exit\": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: stopped(old, test),", r#"
    "loop.exit.call.zero.requires": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: stopped(old, test),
    "loop.exit.local.zero.refined": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, spec: exact(spec),
    "loop.exit": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, value, spec, local_spec: exact(local_spec),"#)
        .replace("    return counter", "    zero: Refined[Nat, lambda v: Eq[Nat, v, 0]] = keep_zero(counter)\n    return zero");
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace("keep_zero(counter)", "keep_zero(1)"),
        TARGET
    )
    .is_err());
}

#[test]
fn loop_exit_infers_bool_contract_results() {
    let helper = "@verified(proof=lambda pre: refl(True_()))\ndef yes() -> Refined[Bool, lambda v: Eq[Bool, v, True_()]]:\n    return True\n\n";
    let source = LOOP.replace("from deppy.data import Bool,", "from deppy.data import True_, Bool,")
        .replace("@verified(proofs={", &format!("{helper}@verified(proofs={{"))
        .replace("    \"loop.exit\": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: stopped(old, test),", r#"
    "loop.exit.call.flag.requires": lambda n, pre, initial, initial_bound, state, inv, test, old, bound: MkUnit(),
    "loop.exit": lambda n, pre, initial, initial_bound, state, inv, test, old, bound, flag, truth: exact(truth),"#)
        .replace("def bounded_countdown(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 0]]:", "def bounded_countdown(n: Nat) -> Refined[Bool, lambda result: Eq[Bool, result, True_()]]:")
        .replace("    return counter", "    flag = yes()\n    return flag");
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(&source.replace("return True", "return False"), TARGET).is_err());
}
