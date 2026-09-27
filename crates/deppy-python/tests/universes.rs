use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, lower_module, Target};

const SOURCE: &str = include_str!("../examples/core/universes.py");

#[test]
fn higher_record_and_recursive_motive_compute_on_all_targets() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let source = SOURCE;
        let m = check_module(source, target).unwrap();
        for (name, expected) in [
            ("carrier", Term::Nat.arc()),
            (
                "unpack",
                Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc(),
            ),
        ] {
            let value = m
                .elaborator
                .infer(&E::name(name).app(E::Zero.succ().succ()))
                .unwrap();
            assert_eq!(
                m.elaborator.kernel().normalize(&value.term).unwrap(),
                expected
            );
        }
        let aliased = source
            .replace("record,", "record as rec,")
            .replace("@record(", "@rec(")
            .replace("dependent,", "dependent as dep,")
            .replace("@dependent", "@dep")
            .replace(
                "decreases=\"n\", motive_level=1",
                "motive_level=1, decreases=\"n\"",
            );
        check_module(&aliased, target).unwrap();
    }
}

#[test]
fn incorrect_universes_and_neutral_carriers_are_rejected() {
    // A neutral carrier(n) does not reduce to Nat.
    assert!(check_module(
        &SOURCE.replace("carrier(2)", "carrier(n)"),
        Target::Python314
    )
    .is_err());
    let source = SOURCE;
    for bad in [
        source.replace("level=1", "level=0"),
        source.replace("motive_level=1", "motive_level=0"),
        source.replace("motive_level=1", "motive_level=2"),
        source.replace("@record(level=1)", "@record(level=4294967295)"),
    ] {
        assert!(check_module(&bad, Target::Python314).is_err(), "{bad}");
    }
}

#[test]
fn decorator_levels_require_literals_and_known_unique_keywords() {
    for level in ["-1", "True", "1.0", "'1'", "Nat", "1 + 0", "4294967296"] {
        for bad in [
            SOURCE.replace("@record(level=1)", &format!("@record(level={level})")),
            SOURCE.replace("motive_level=1", &format!("motive_level={level}")),
        ] {
            assert!(lower_module(&bad, Target::Python314).is_err(), "{bad}");
        }
    }
    for (old, new) in [
        ("@record(level=1)", "@record(1)"),
        ("@record(level=1)", "@record(other=1)"),
        ("@record(level=1)", "@record(level=1, level=1)"),
        ("@record(level=1)", "@record(**options)"),
        ("decreases=\"n\", motive_level=1", "motive_level=1"),
        (
            "decreases=\"n\", motive_level=1",
            "decreases=\"n\", other=1",
        ),
        (
            "decreases=\"n\", motive_level=1",
            "decreases=\"n\", motive_level=1, motive_level=1",
        ),
    ] {
        assert!(
            lower_module(&SOURCE.replace(old, new), Target::Python314).is_err(),
            "{new}"
        );
    }
}
