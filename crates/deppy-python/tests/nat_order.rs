use deppy_python::{check_module, Target};

const HEADER: &str = r#"from __future__ import annotations
from deppy import dependent, Type, Nat, S, Eq, refl, absurd
from deppy.nat import add, pred_or
from deppy.data import Empty, decision_weight
from deppy.nat_order import LE, LT, LEZero, LESucc, le_decide, lt_decide, le_refl, le_step, le_antisymm, lt_irrefl, lt_trans, add_le_add_left, add_le_add_right, add_lt_add_right, pred_lt
"#;

#[test]
fn order_decisions_compute_on_both_sides_of_the_boundary() {
    let mut source = HEADER.to_owned();
    for n in 0..4 {
        for m in 0..4 {
            for (name, expected) in [("le_decide", n <= m), ("lt_decide", n < m)] {
                source.push_str(&format!(
                    "\n@dependent\ndef {name}_{n}_{m}() -> Eq[Nat, decision_weight({name}({n}, {m})), {}]:\n    return refl({})\n",
                    usize::from(expected), usize::from(expected)
                ));
            }
        }
    }
    let checked = check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    // A wrong result must fail even though the decision carries proof fields.
    let bad = format!("{HEADER}\n@dependent\ndef bad() -> Eq[Nat, decision_weight(le_decide(2, 1)), 1]:\n    return refl(1)\n");
    assert!(check_module(&bad, Target::Python314).is_err());
}

#[test]
fn bounds_and_countdown_obligations_are_axiom_free() {
    let source = format!(
        "{HEADER}{}",
        r#"
@dependent
def bounds(n: Nat, m: Nat, p: LE[n, m], q: LE[m, n]) -> Eq[Nat, n, m]:
    return le_antisymm(p, q)

@dependent
def prefix(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[add(k, n), add(k, m)]:
    return add_le_add_left(n, m, k, p)

@dependent
def suffix(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[add(n, k), add(m, k)]:
    return add_le_add_right(p, k)

@dependent
def strict_suffix(n: Nat, m: Nat, k: Nat, p: LT(n, m)) -> LT(add(n, k), add(m, k)):
    return add_lt_add_right(n, m, k, p)

@dependent
def descent(n: Nat, p: LT(0, n)) -> LT(pred_or(0, n), n):
    return pred_lt(n, p)

@dependent
def no_cycle(n: Nat, m: Nat, p: LT(n, m), q: LT(m, n)) -> Empty:
    return lt_irrefl(n, lt_trans(n, m, n, p, q))

@dependent
def one_step(n: Nat) -> LT(pred_or(0, S(n)), S(n)):
    return pred_lt(S(n), LESucc(0, n, LEZero(n)))
"#
    );
    let checked = check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    for body in [
        "def bad(n: Nat) -> LT(n, n):\n    return le_refl(n)",
        "def bad() -> LT(pred_or(0, 0), 0):\n    return pred_lt(0, le_refl(0))",
        "def bad(n: Nat, m: Nat, p: LE[n, m]) -> LE[S(n), m]:\n    return le_step(p)",
    ] {
        assert!(check_module(
            &format!("{HEADER}\n@dependent\n{body}\n"),
            Target::Python314
        )
        .is_err());
    }
}

#[test]
fn absurd_eliminates_only_constructor_disjoint_indexed_families() {
    let source = format!(
        "{HEADER}{}",
        r#"
@dependent
def empty_target[A: Type](n: Nat, p: LE[S(n), 0]) -> A:
    return absurd(A, p)

@dependent
def higher_target(n: Nat, p: LE[S(n), 0]) -> Type:
    return absurd(Type, p)
"#
    );
    let checked = check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    for ty in ["LE[0, n]", "LE[n, n]", "LE[S(n), S(n)]", "LE[n, 0]", "Nat"] {
        let source = format!("{HEADER}\n@dependent\ndef bad(n: Nat, p: {ty}) -> Empty:\n    return absurd(Empty, p)\n");
        assert!(check_module(&source, Target::Python314).is_err(), "{ty}");
    }
}
