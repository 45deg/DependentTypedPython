use deppy_python::{check_module, Target};

const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, Eq, refl, Nat\nfrom deppy.bool import Bool, False_, True_, negate, conjunction, disjunction, xor, eq_decide\nfrom deppy.data import decision_weight\n";

#[test]
fn boolean_library_laws_are_checked_without_axioms() {
    let checked = check_module(include_str!("../stdlib/deppy/bool.py"), Target::Python314).unwrap();
    for name in [
        "negate_involutive",
        "conjunction_distrib",
        "disjunction_distrib",
        "negate_conjunction",
        "negate_disjunction",
        "is_true_intro",
        "is_true_elim",
        "eq_decide",
    ] {
        assert!(checked.interface.exports().contains_key(name), "{name}");
    }
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn exhaustive_truth_tables_and_equality_decisions_compute() {
    let boolean = |value| if value { "True_()" } else { "False_()" };
    let mut source = HEADER.to_owned();
    let mut index = 0;
    for a in [false, true] {
        let av = boolean(a);
        let negated = boolean(!a);
        source.push_str(&format!(
            "\n@dependent\ndef neg_{index}() -> Eq[Bool, negate({av}), {negated}]:\n    return refl({negated})\n"
        ));
        for b in [false, true] {
            let bv = boolean(b);
            for (op, expected) in [
                ("conjunction", a && b),
                ("disjunction", a || b),
                ("xor", a ^ b),
            ] {
                let result = boolean(expected);
                source.push_str(&format!(
                    "\n@dependent\ndef table_{index}() -> Eq[Bool, {op}({av}, {bv}), {result}]:\n    return refl({result})\n"
                ));
                index += 1;
            }
            let weight = usize::from(a == b);
            source.push_str(&format!(
                "\n@dependent\ndef decision_{index}() -> Eq[Nat, decision_weight(eq_decide({av}, {bv})), {weight}]:\n    return refl({weight})\n"
            ));
        }
    }
    check_module(&source, Target::Python314).unwrap();
}

#[test]
fn false_boolean_equations_are_rejected() {
    for expression in [
        "negate(False_())",
        "conjunction(True_(), True_())",
        "disjunction(False_(), True_())",
        "xor(False_(), True_())",
    ] {
        let source = format!(
            "{HEADER}\n@dependent\ndef invalid() -> Eq[Bool, {expression}, False_()]:\n    return refl(False_())\n"
        );
        let error = check_module(&source, Target::Python314).err().unwrap();
        assert!(!error.message.contains("budget"), "{}", error.message);
        assert!(!error.message.contains("import"), "{}", error.message);
    }
}
