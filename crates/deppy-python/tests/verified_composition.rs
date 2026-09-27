use deppy_python::{analyze_module, check_module, check_module_with_resolver, Target};
const TARGET: Target = Target::Python314;
const EXAMPLE: &str = include_str!("../examples/verified/verified_composition.py");
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, theorem, Nat, S, Eq, refl\nfrom deppy.data import Bool, Unit, MkUnit, True_, False_\nfrom deppy.verified import verified, Refined, verified_spec\n";

#[test]
fn contracts_compose_and_cannot_use_callee_implementation_to_prove_continuation() {
    let checked = check_module(EXAMPLE, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    assert!(checked.interface.exports()["composed"]
        .verified_spec
        .is_some());
    for (from, to) in [
        ("first = zero_to_one(n)", "first = zero_to_one(1)"),
        ("second = one_to_two(first)", "second = one_to_two(n)"),
        ("second_spec: second_spec", "second_spec: refl(2)"),
        ("first_spec: first_spec", "first_spec: refl(1)"),
        ("return second", "return first"),
        (
            "second = one_to_two(first)",
            "first = 0\n    second = one_to_two(first)",
        ),
        (
            "verified_spec(composed, 0, refl(0))",
            "verified_spec(composed, 1, refl(1))",
        ),
    ] {
        assert!(
            check_module(&EXAMPLE.replace(from, to), TARGET).is_err(),
            "{from} -> {to}"
        );
    }
}

#[test]
fn missing_proofs_are_separate_named_goals_at_call_and_return_sites() {
    let start = EXAMPLE.find("    proofs={").unwrap();
    let end = start + EXAMPLE[start..].find("    },").unwrap() + 6;
    let mut source = EXAMPLE.to_owned();
    source.replace_range(start..end, "    auto=False, proofs={},");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    let names = analysis
        .goals
        .iter()
        .map(|g| g.name.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            "composed.call.first.requires",
            "composed.call.second.requires",
            "composed.return"
        ],
        "{:?}",
        analysis.diagnostics
    );
    for (goal, site) in analysis
        .goals
        .iter()
        .zip(["zero_to_one(n)", "one_to_two(first)", "second"])
    {
        let location = goal.location.as_ref().unwrap();
        assert_eq!(&source[location.start..location.end], site);
        assert!(goal.context.iter().any(|c| c.name == "n"));
    }
    let second = &analysis.goals[1];
    assert!(second
        .context
        .iter()
        .any(|c| c.name.starts_with("$call_spec")));
    assert!(second.expected.contains("Eq"), "{}", second.expected);
}

#[test]
fn imported_reexported_contracts_preserve_preconditions_and_axioms() {
    let library = EXAMPLE[..EXAMPLE
        .find("@verified(\n    requires=lambda n: Eq[Nat, n, 0],\n    proofs=")
        .unwrap()]
        .to_owned();
    let source = format!("{HEADER}from facade import step as advance\n@verified(requires=lambda n: Eq[Nat, n, 0], proofs={{'call.y.requires': lambda n, pre: pre, 'return': lambda n, pre, y, spec: spec}})\ndef caller(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 1]]:\n    y = advance(n)\n    return y\n");
    let mut resolver = |name: &str| {
        Ok(match name {
            "library" => Some(library.clone()),
            "facade" => Some("from library import zero_to_one as step\n".into()),
            _ => None,
        })
    };
    check_module_with_resolver(&source, TARGET, &mut resolver).unwrap_or_else(|e| panic!("{e}"));
    let changed = source.replace("advance(n)", "advance(1)");
    assert!(check_module_with_resolver(&changed, TARGET, &mut resolver).is_err());
    let axiom_library = format!("{HEADER}from deppy import axiom\n@axiom\ndef trusted(n: Nat) -> Eq[Nat, n, 1]:\n    ...\n@verified(proof=lambda n, pre: trusted(n))\ndef unsafe(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 1]]:\n    return n\n");
    let source = source
        .replace(
            "from facade import step as advance",
            "from library import unsafe as advance",
        )
        .replace("lambda n, pre: pre", "lambda n, pre: MkUnit()");
    let checked = check_module_with_resolver(&source, TARGET, &mut |_: &str| {
        Ok(Some(axiom_library.clone()))
    })
    .unwrap();
    assert!(checked.axiom_dependencies["caller"]
        .iter()
        .any(|a| a.contains("trusted")));
}

#[test]
fn branches_reassignment_bool_and_nullary_calls_use_current_values() {
    let source = format!(
        "{HEADER}{}",
        r#"
@verified(proof=lambda flag, pre: refl(flag))
def keep(flag: Bool) -> Refined[Bool, lambda r: Eq[Bool, r, flag]]:
    return flag
@verified(proof=lambda pre: refl(0))
def zero() -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return 0
@verified(proofs={
    'call.flag.requires': lambda flag, pre: MkUnit(),
    'call.flag.2.requires': lambda flag, pre, first, first_spec: MkUnit(),
    'then.call.return.requires': lambda flag, pre, first, first_spec, second, second_spec, branch: MkUnit(),
    'then.return': lambda flag, pre, first, first_spec, second, second_spec, branch, value, spec: spec,
    'else.return': lambda flag, pre, first, first_spec, second, second_spec, branch: refl(0),
})
def choose(flag: Bool) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    flag = keep(flag)
    flag = keep(flag)
    if flag:
        return zero()
    return 0
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace("flag = keep(flag)", "flag: Nat = keep(flag)"),
        TARGET
    )
    .is_err());
}

#[test]
fn proof_maps_and_untracked_call_forms_fail_closed() {
    for (from, to) in [
        ("proofs={", "proof=lambda n, pre: refl(2), proofs={"),
        ("\"call.first.requires\"", "\"typo\""),
        ("\"call.first.requires\": lambda n, pre: pre,", "\"call.first.requires\": lambda n, pre: pre, \"call.first.requires\": lambda n, pre: pre,"),
        ("first = zero_to_one(n)", "first = S(zero_to_one(n))"),
        ("first = zero_to_one(n)", "first = zero_to_one(n=n)"),
        ("first = zero_to_one(n)", "first = zero_to_one()"),
        ("first = zero_to_one(n)", "first, other = zero_to_one(n), n"),
        ("first = zero_to_one(n)", "first = zero_to_one(n)\n    zero_to_one = n"),
    ] {
        assert!(check_module(&EXAMPLE.replace(from, to), TARGET).is_err(), "{from} -> {to}");
    }
    let source = format!("{HEADER}@verified(proof=lambda n, pre: refl(n))\ndef identity(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    return n\n@verified(proof=lambda n, pre: refl(n))\ndef unchecked(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    return identity(n)\n");
    assert!(check_module(&source, TARGET).is_err());
}

#[test]
fn named_loop_goals_and_proofs_keep_the_four_totality_obligations() {
    let source = format!("{HEADER}from deppy.verified_loop import invariant, decreases\n@verified(auto=False, proofs={{}})\ndef loop(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    x = n\n    while False:\n        invariant(lambda x: Eq[Nat, x, n], state=(x,))\n        decreases(lambda x: x)\n        x = x\n    return x\n");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(
        analysis
            .goals
            .iter()
            .map(|g| g.name.as_str())
            .collect::<Vec<_>>(),
        [
            "loop.loop.init",
            "loop.loop.preserve",
            "loop.loop.decrease",
            "loop.loop.exit"
        ],
        "{:?}",
        analysis.diagnostics
    );
    let source = source.replace("from deppy import dependent", "from deppy import absurd, dependent").replace("from deppy.verified import verified", "from deppy.verified import false_ne_true, verified").replace("proofs={}", r#"proofs={
        'loop.init': lambda n, pre: refl(n),
        'loop.preserve': lambda n, pre, state, inv, test: inv,
        'loop.decrease': lambda n, pre, state, inv, test: absurd(LT(state.fst, state.fst), false_ne_true(test)),
        'loop.exit': lambda n, pre, state, inv, test: inv,
    }"#).replace("from deppy.verified_loop import", "from deppy.nat_order import LT\nfrom deppy.verified_loop import");
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn contract_changes_invalidate_cached_composition() {
    let library = format!("{HEADER}@verified(proof=lambda n, pre: refl(n))\ndef identity(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    return n\n");
    let source = format!("{HEADER}from library import identity\n@verified(proofs={{'call.y.requires': lambda n, pre: MkUnit(), 'return': lambda n, pre, y, spec: spec}})\ndef caller(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:\n    y = identity(n)\n    return y\n");
    let mut session = deppy_python::CheckSession::default();
    for _ in 0..2 {
        session
            .check(&source, Default::default(), &mut |_: &str| {
                Ok(Some(library.clone()))
            })
            .unwrap();
    }
    assert!(session.reused_declarations() > 0);
    for changed in [
        library
            .replace("r, n]", "r, S(n)]")
            .replace("refl(n)", "refl(S(n))")
            .replace("return n", "return S(n)"),
        library.replace("@verified(", "@verified(requires=lambda n: Eq[Nat, n, 0], "),
    ] {
        assert!(session
            .check(&source, Default::default(), &mut |_: &str| Ok(Some(
                changed.clone()
            )))
            .is_err());
        assert_eq!(session.reused_declarations(), 0);
    }
}

#[test]
fn loop_contracts_can_be_used_by_modular_callers() {
    let source = format!("{HEADER}from fibonacci import fib_loop, fib_recursive\n@verified(proofs={{'call.result.requires': lambda n, pre: MkUnit(), 'return': lambda n, pre, result, spec: spec}})\ndef fib_client(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, fib_recursive(n)]]:\n    result = fib_loop(n)\n    return result\n");
    let checked = check_module_with_resolver(&source, TARGET, &mut |name: &str| {
        Ok((name == "fibonacci")
            .then(|| include_str!("../examples/verified/fibonacci.py").to_owned()))
    })
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies["fib_client"].is_empty());
}

#[test]
fn proof_callbacks_support_checked_lemmas_and_hygienic_type_binders() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy import ann, Pi
@verified(proof=lambda flag, pre: refl(flag))
def keep(flag: Bool) -> Refined[Bool, lambda r: Eq[Bool, r, flag]]:
    return flag
@verified(proofs={
    'call.flag.requires': lambda flag, pre: MkUnit(),
    'return': lambda flag, pre, r, spec: ann(lambda r: refl(r), Pi[Nat, lambda r: Eq[Nat, r, r]])(0),
})
def shadow(flag: Bool) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    flag = keep(flag)
    return 0
@theorem
def finish(flag: Bool, pre: Unit) -> Eq[Nat, 0, 0]:
    return refl(0)
@verified(proofs={'return': finish})
def constant(flag: Bool) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    return 0
"#
    );
    check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
}
