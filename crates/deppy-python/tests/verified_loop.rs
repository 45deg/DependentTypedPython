use deppy_python::{analyze_module, check_module, Target};
const TARGET: Target = Target::Python314;
const EXAMPLE: &str = include_str!("../examples/verified/verified_loop.py");

#[test]
fn loops_prove_result_and_termination_and_compute() {
    let mut source = EXAMPLE.replace(
        "from deppy import theorem",
        "from deppy import dependent, theorem",
    );
    for n in [0, 1, 2, 5] {
        source.push_str(&format!("\n@dependent\ndef countdown_{n}() -> Eq[Nat, countdown({n}), 0]:\n    return refl(0)\n\n@dependent\ndef accumulate_{n}() -> Eq[Nat, accumulate({n}), {n}]:\n    return refl({n})\n"));
    }
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn wrong_preservation_exit_and_nontermination_are_rejected() {
    for (from, to) in [
        ("counter = pred_or(0, counter)", "counter = counter"),
        ("counter = pred_or(0, counter)", "counter = S(counter)"),
        ("total = S(total)", "total = total"),
        (
            "decreases(lambda counter: counter)",
            "decreases(lambda counter: 0)",
        ),
        (
            "decreases(lambda counter, total: counter)",
            "decreases(lambda counter, total: total)",
        ),
        ("total = 0", "total = 1"),
        ("return total", "return S(total)"),
        ("while 0 < counter:", "while 0 <= counter:"),
        (
            "ensures=lambda n, result: Eq[Nat, result, 0]",
            "ensures=lambda n, result: Eq[Nat, result, 1]",
        ),
    ] {
        assert!(EXAMPLE.contains(from));
        assert!(
            check_module(&EXAMPLE.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}

#[test]
fn annotations_scope_and_unsupported_control_flow_are_rejected() {
    for (from, to) in [
        ("        decreases(lambda counter: counter)\n", ""),
        ("state=(counter,)", "state=(missing,)"),
        ("state=(counter,)", "state=(counter, counter)"),
        ("state=(counter, total)", "state=(counter,)"),
        (
            "decreases(lambda counter: counter)",
            "decreases(lambda counter: False_())",
        ),
        ("counter = pred_or(0, counter)", "counter = True"),
        ("counter = pred_or(0, counter)", "return counter"),
        ("counter = pred_or(0, counter)", "break"),
        ("counter = pred_or(0, counter)", "continue"),
        (
            "    return counter",
            "    else:\n        counter = 0\n    return counter",
        ),
        ("counter = pred_or(0, counter)", "undeclared = counter"),
    ] {
        assert!(
            check_module(&EXAMPLE.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}

#[test]
fn each_loop_obligation_can_be_presented_as_a_goal() {
    let source = EXAMPLE
        .replace("from deppy import theorem", "from deppy import hole, theorem")
        .replace("lambda state, inv, test: pred_lt(state.fst, decision_true(lt_decide(0, state.fst), test))", "lambda state, inv, test: hole(\"decrease_vc\")");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert!(analysis.goals.iter().any(|goal| goal.name == "decrease_vc"));
}

#[test]
fn branches_in_the_transition_and_continuation_are_interpreted() {
    let source = EXAMPLE.replace(
        "        total = S(total)",
        "        if 0 < counter:\n            total = S(total)\n        else:\n            total = S(total)",
    );
    // A symbolic branch changes the denotation even if both arms agree; the old
    // hand proof need not be definitionally equal. Concrete branches do reduce.
    let source = source
        .replace("        if 0 < counter:", "        if True:")
        .replace(
            "    return total",
            "    if False:\n        return 0\n    else:\n        return total",
        );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn generic_loop_theorems_are_axiom_free() {
    let checked = check_module(include_str!("../stdlib/deppy/verified_loop.py"), TARGET)
        .unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn zero_iteration_loop_preserves_mixed_scalar_state() {
    let source = r#"from deppy import dependent, Nat, Eq, refl, Pair, absurd
from deppy.data import Bool, False_, Unit, MkUnit
from deppy.nat_order import LT
from deppy.verified import verified, false_ne_true
from deppy.verified_loop import invariant, decreases
@verified(ensures=lambda result: Unit, proof=lambda pre: Pair(MkUnit(), Pair(lambda s, inv, test: MkUnit(), Pair(lambda s, inv, test: absurd(LT(s.fst, s.fst), false_ne_true(test)), lambda s, inv, test: MkUnit()))))
def never() -> Bool:
    counter = 0
    flag = False
    while False:
        invariant(lambda counter, flag: Unit, state=(counter, flag))
        decreases(lambda counter, flag: counter)
        flag = True
        counter = counter
    return flag
@dependent
def computed() -> Eq[Bool, never(), False_()]:
    return refl(False_())
"#;
    check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn loop_certificate_axioms_remain_visible() {
    let source = EXAMPLE
        .replace(
            "from deppy import theorem",
            "from deppy import axiom, theorem",
        )
        .replace(
            "@verified(",
            "@axiom\ndef trusted_zero(n: Nat) -> Eq[Nat, n, 0]:\n    ...\n\n@verified(",
        )
        .replace(
            "stopped_at_zero(state.fst, test)",
            "trusted_zero(state.fst)",
        );
    // Keep the first function and its helpers; avoid declaring the test axiom twice.
    let source = source
        .split("@theorem(decreases=\"counter\")")
        .next()
        .unwrap();
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(
        checked.axiom_dependencies["countdown"],
        vec!["trusted_zero"]
    );
}
