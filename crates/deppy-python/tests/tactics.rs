use deppy_python::{analyze_module, check_module, Target};
const TARGET: Target = Target::Python314;
const HEADER: &str = "from __future__ import annotations\nfrom deppy import theorem, Nat, Z, S, Type, Eq, Pi, refl, hole\nfrom deppy.tactics import intro, exact, apply, rewrite, rewrite_in, cases, induction\n";

#[test]
fn small_tactics_generate_checked_axiom_free_terms() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy.nat import add, add_zero
from deppy.equality import sym
from deppy.data import Bool, False_, True_
@theorem
def identity() -> Pi[Nat, lambda n: Eq[Nat, n, n]]:
    return intro(lambda n: exact(refl(n)))
@theorem
def use_lemma(n: Nat) -> Eq[Nat, add(n, 0), n]:
    return apply(add_zero, n)
@theorem
def rewrite_goal(a: Nat, b: Nat, p: Eq[Nat, a, b]) -> Eq[Nat, S(a), S(b)]:
    return rewrite(p, refl(S(b)))
@theorem
def rewrite_hypothesis(a: Nat, b: Nat, p: Eq[Nat, a, b], q: Eq[Nat, S(a), 0]) -> Eq[Nat, S(b), 0]:
    return rewrite_in(p, q)
@theorem
def split(n: Nat) -> Eq[Nat, n, n]:
    return cases(n, {Z: refl(0), S: lambda k: refl(S(k))})
@theorem
def split_bool(b: Bool) -> Eq[Bool, b, b]:
    return cases(b, {False_: refl(False_()), True_: refl(True_())})
@theorem
def by_induction(n: Nat) -> Eq[Nat, add(n, 0), n]:
    return induction(0, n, lambda k: Eq[Nat, add(k, 0), k], refl(0), lambda k, ih: rewrite(ih, refl(S(k))))
@theorem
def under_binder(a: Nat, b: Nat, p: Eq[Nat, a, b]) -> Pi[Nat, lambda a: Eq[Nat, b, b]]:
    return rewrite(sym(p), intro(lambda k: refl(a)))
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn tactics_reject_invalid_proofs_and_incomplete_cases() {
    for body in [
        "rewrite(refl(0), refl(1))",
        "rewrite(0, refl(0))",
        "rewrite_in(refl(0), refl(1))",
        "exact(refl(1))",
        "apply(refl(1))",
        "intro(refl(0))",
        "cases(0, {Z: refl(0)})",
        "cases(0, {Z: refl(0), Z: refl(0), S: lambda k: refl(0)})",
        "induction(0, 0, lambda n: Eq[Nat, n, n], refl(0), lambda k, ih: refl(k))",
    ] {
        let source = format!("{HEADER}@theorem\ndef bad() -> Eq[Nat, 0, 0]:\n    return {body}\n");
        assert!(check_module(&source, TARGET).is_err(), "accepted {body}");
    }
}

#[test]
fn rewritten_goals_keep_source_and_context_and_cannot_be_exported() {
    let source = format!("{HEADER}@theorem\ndef pending(a: Nat, b: Nat, p: Eq[Nat, a, b]) -> Eq[Nat, a, b]:\n    return rewrite(p, hole('after_rewrite'))\n");
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    let goal = &analysis.goals[0];
    assert_eq!(goal.name, "after_rewrite");
    assert_eq!(goal.expected, "Eq[Nat, b, b]");
    assert!(goal.context.iter().any(|local| local.name == "p"));
    let location = goal.location.as_ref().unwrap();
    assert_eq!(
        &source[location.start..location.end],
        "hole('after_rewrite')"
    );
    assert!(check_module(&source, TARGET).is_err());
}

#[test]
fn fibonacci_rewrites_and_independent_loop_goals_are_checked() {
    let source = include_str!("../examples/fibonacci.py");
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let start = source.find("    proofs={").unwrap();
    let end = start + source[start..].find("    },").unwrap() + "    },".len();
    let mut incomplete = source.to_owned();
    incomplete.replace_range(start..end, "    proofs={},");
    // Stop before clients of the deliberately unfinished declaration.
    incomplete.truncate(incomplete.find("@theorem\ndef fib_loop_correct").unwrap());
    let analysis = analyze_module(&incomplete, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 4, "{:?}", analysis.diagnostics);
    for (goal, suffix) in analysis
        .goals
        .iter()
        .zip(["init", "preserve", "decrease", "exit"])
    {
        assert_eq!(goal.name, format!("fib_loop.loop.{suffix}"));
        let location = goal.location.as_ref().unwrap();
        assert!(location.start < location.end && location.end <= incomplete.len());
        assert!(goal.context.iter().any(|local| local.name == "n"));
        assert!(!goal.expected.is_empty());
        let snippet = &incomplete[location.start..location.end];
        match suffix {
            "init" | "preserve" => assert!(snippet.contains("FibInvariant")),
            "decrease" => assert_eq!(snippet, "lambda remaining, index, a, b: remaining"),
            "exit" => assert_eq!(snippet, "a"),
            _ => unreachable!(),
        }
    }
    assert!(check_module(&incomplete, TARGET).is_err());
    assert!(check_module(
        &source.replace(
            "rewrite(inv.snd.fst, rewrite(inv.snd.snd, fib_step(index)))",
            "refl(0)"
        ),
        TARGET
    )
    .is_err());
}

#[test]
fn rewrites_preserve_axiom_dependencies_and_support_higher_universes() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy import axiom
@axiom
def assumed(a: Nat, b: Nat) -> Eq[Nat, a, b]:
    ...
@theorem
def using_axiom(a: Nat, b: Nat) -> Eq[Nat, a, b]:
    return rewrite(assumed(a, b), refl(b))
@theorem
def types(A: Type, B: Type, p: Eq[Type, A, B]) -> Pi[A, lambda _: B]:
    return rewrite(p, intro(lambda x: x))
"#
    );
    let checked = check_module(&source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(checked.axiom_dependencies["using_axiom"], vec!["assumed"]);
    assert!(checked.axiom_dependencies["types"].is_empty());
}

#[test]
fn a_named_vc_can_be_filled_with_tactics_without_hiding_other_goals() {
    let source = format!(
        "{HEADER}{}",
        r#"
from deppy.verified import verified, Refined
from deppy.verified_loop import invariant, decreases
@verified(proofs={"loop.init": lambda n, pre: exact(refl(n))})
def pending_loop(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, n]]:
    x = n
    while False:
        invariant(lambda x: Eq[Nat, x, n], state=(x,))
        decreases(lambda x: x)
        x = x
    return x
"#
    );
    let analysis = analyze_module(&source, TARGET);
    assert!(analysis.checked.is_none());
    assert_eq!(
        analysis
            .goals
            .iter()
            .map(|g| g.name.as_str())
            .collect::<Vec<_>>(),
        [
            "pending_loop.loop.preserve",
            "pending_loop.loop.decrease",
            "pending_loop.loop.exit"
        ]
    );
}
