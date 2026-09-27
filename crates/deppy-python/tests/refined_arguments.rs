use deppy_python::{
    analyze_module, check_module, check_module_with_resolver, CheckSession, Target,
};
const TARGET: Target = Target::Python314;
const EXAMPLE: &str = include_str!("../examples/verified/refined_arguments.py");
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, theorem, Nat, Eq, refl, Pair\nfrom deppy.data import Bool, True_, Unit, MkUnit\nfrom deppy.verified import verified, Refined, verified_spec\nfrom deppy.tactics import exact\n";

#[test]
fn refined_contracts_compose_with_tactics_and_reject_false_evidence() {
    let checked = check_module(EXAMPLE, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    for (from, to) in [
        ("first = zero_to_one(n)", "first = zero_to_one(1)"),
        (
            "second = one_to_two(first)",
            "first = 0\n    second = one_to_two(first)",
        ),
        ("exact(first_spec)", "exact(pre)"),
        (
            "verified_spec(composed, 0, refl(0))",
            "verified_spec(composed, 1, refl(1))",
        ),
        (
            "verified_spec(composed, 0, refl(0))",
            "verified_spec(composed, 0, 0)",
        ),
    ] {
        assert!(
            check_module(&EXAMPLE.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}

#[test]
fn missing_call_condition_is_a_named_goal_and_tactic_fills_it() {
    let source = EXAMPLE
        .replace(
            "    \"call.first.requires\": lambda n, pre: exact(pre),\n",
            "",
        )
        .replace("proofs={", "auto=False, proofs={");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    let goal = &analysis.goals[0];
    assert_eq!(goal.name, "composed.call.first.requires");
    let location = goal.location.as_ref().unwrap();
    assert_eq!(&source[location.start..location.end], "zero_to_one(n)");
    assert!(goal.expected.contains("Eq"));
    assert!(goal
        .context
        .iter()
        .any(|c| c.name == "$pre" && c.ty.contains("Eq")));
    check_module(EXAMPLE, TARGET).unwrap();
    // A plain Nat caller has no refinement assumption: the goal remains, and
    // exact(pre) cannot turn the default Unit evidence into the missing equality.
    let plain = source.replace(
        "def composed(n: Refined[Nat, lambda value: Eq[Nat, value, 0]])",
        "def composed(n: Nat)",
    );
    assert_eq!(analyze_module(&plain, TARGET).goals[0].name, goal.name);
    assert!(check_module(
        &EXAMPLE.replace(
            "def composed(n: Refined[Nat, lambda value: Eq[Nat, value, 0]])",
            "def composed(n: Nat)"
        ),
        TARGET
    )
    .is_err());
}

#[test]
fn dependent_parameter_conditions_and_explicit_requires_have_stable_pair_order() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(requires=lambda limit, n, flag: Eq[Nat, limit, 0], proof=lambda limit, n, flag, pre: pre.fst)
def same(limit: Nat, n: Refined[Nat, lambda x: Eq[Nat, x, limit]], flag: Refined[Bool, lambda b: Eq[Bool, b, True_()]]) -> Refined[Nat, lambda r: Eq[Nat, r, limit]]:
    limit = 1
    return n
@theorem
def use() -> Eq[Nat, same(0, 0, True_()), 0]:
    return verified_spec(same, 0, 0, True_(), Pair(refl(0), Pair(refl(True_()), refl(0))))
@verified(proofs={
    'call.result.requires': lambda limit, n, flag, pre: exact(pre),
    'return': lambda limit, n, flag, pre, result, spec: exact(spec),
}, requires=lambda limit, n, flag: Eq[Nat, limit, 0])
def forward(limit: Nat, n: Refined[Nat, lambda x: Eq[Nat, x, limit]], flag: Refined[Bool, lambda b: Eq[Bool, b, True_()]]) -> Refined[Nat, lambda r: Eq[Nat, r, limit]]:
    result = same(limit, n, flag)
    return result
@verified(proof=lambda n, flag, pre: pre.snd)
def pair_only(n: Refined[Nat, lambda x: Eq[Nat, x, 0]], flag: Refined[Bool, lambda b: Eq[Bool, b, True_()]]) -> Refined[Bool, lambda r: Eq[Bool, r, True_()]]:
    return flag
@theorem
def use_pair() -> Eq[Bool, pair_only(0, True_()), True_()]:
    return verified_spec(pair_only, 0, True_(), Pair(refl(0), refl(True_())))
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace(
            "result = same(limit, n, flag)",
            "limit = 1\n    result = same(limit, n, flag)"
        ),
        TARGET
    )
    .is_err());
    assert!(check_module(
        &source.replace(
            "Pair(refl(0), Pair(refl(True_()), refl(0)))",
            "Pair(refl(0), Pair(refl(0), refl(True_())))"
        ),
        TARGET
    )
    .is_err());
}

#[test]
fn malformed_predicates_forward_references_and_local_refinements_are_rejected() {
    let source = format!("{HEADER}@verified(proof=lambda n, pre: refl(n))\ndef keep(n: Refined[Nat, lambda x: Eq[Nat, x, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    return n\n");
    for bad in [
        source.replace("lambda x: Eq[Nat, x, 0]", "lambda x: 0"),
        source.replace("lambda x: Eq[Nat, x, 0]", "lambda x, y: Unit"),
        source.replace("Refined[Nat, lambda x: Eq[Nat, x, 0]]", "Refined[Nat]"),
        source.replace(
            "Refined[Nat, lambda x: Eq[Nat, x, 0]]",
            "Refined[Unit, lambda x: Unit]",
        ),
        source.replace("Eq[Nat, x, 0]", "Eq[Nat, x, n]"),
        source
            .replace("Eq[Nat, x, 0]", "Eq[Nat, x, later]")
            .replace("]) ->", "], later: Nat) ->"),
        source.replace(
            "    return n",
            "    x: Refined[Nat, lambda v: Unit] = n\n    return x",
        ),
    ] {
        assert!(check_module(&bad, TARGET).is_err(), "{bad}");
    }
    // A predicate's own binder may shadow the parameter being annotated.
    check_module(
        &source.replace("lambda x: Eq[Nat, x, 0]", "lambda n: Eq[Nat, n, 0]"),
        TARGET,
    )
    .unwrap();
    check_module(
        &source
            .replace("Refined", "R")
            .replace("import verified, R,", "import verified, Refined as R,"),
        TARGET,
    )
    .unwrap();
}

#[test]
fn imported_contract_changes_invalidate_cached_parameter_obligations() {
    let library = format!("{HEADER}@verified(proof=lambda n, pre: pre)\ndef zero(n: Refined[Nat, lambda x: Eq[Nat, x, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return n\n");
    let source = format!("{HEADER}from facade import step as zero\n@verified(proofs={{'call.y.requires': lambda n, pre: exact(pre), 'return': lambda n, pre, y, spec: exact(spec)}})\ndef client(n: Refined[Nat, lambda x: Eq[Nat, x, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    y = zero(n)\n    return y\n");
    let facade = "from library import zero as step\n";
    let mut session = CheckSession::default();
    for _ in 0..2 {
        session
            .check(&source, Default::default(), &mut |name: &str| {
                Ok(Some(if name == "facade" {
                    facade.into()
                } else {
                    library.clone()
                }))
            })
            .unwrap();
    }
    assert!(session.reused_declarations() > 0);
    let changed = library
        .replace("x, 0]", "x, 1]")
        .replace("proof=lambda n, pre: pre", "proof=lambda n, pre: refl(0)")
        .replace("return n", "return 0");
    assert!(session
        .check(&source, Default::default(), &mut |name: &str| Ok(Some(
            if name == "facade" {
                facade.into()
            } else {
                changed.clone()
            }
        )))
        .is_err());
    assert_eq!(session.reused_declarations(), 0);
}

#[test]
fn refined_inputs_work_with_loop_certificates_and_axiom_tracking() {
    let fib = include_str!("../examples/verified/fibonacci.py")
        .replace(
            "def fib_loop(n: Nat)",
            "def fib_loop(n: Refined[Nat, lambda x: Eq[Nat, x, x]])",
        )
        .replace(
            "verified_spec(fib_loop, n, MkUnit())",
            "verified_spec(fib_loop, n, refl(n))",
        );
    check_module(&fib, TARGET).unwrap_or_else(|e| panic!("{e}"));
    let library = format!("{HEADER}from deppy import axiom\n@axiom\ndef trust(n: Nat) -> Eq[Nat, n, 0]:\n    ...\n@verified(proof=lambda n, pre: pre)\ndef zero(n: Refined[Nat, lambda x: Eq[Nat, x, 0]]) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    return n\n");
    let source = format!("{HEADER}from library import zero, trust\n@verified(proofs={{'call.y.requires': lambda n, pre: trust(n), 'return': lambda n, pre, y, spec: exact(spec)}})\ndef client(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:\n    y = zero(n)\n    return y\n");
    let checked =
        check_module_with_resolver(&source, TARGET, &mut |_: &str| Ok(Some(library.clone())))
            .unwrap();
    assert!(checked.axiom_dependencies["client"]
        .iter()
        .any(|a| a.contains("trust")));
}
