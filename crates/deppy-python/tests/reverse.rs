use deppy_elab::Expr as E;
use deppy_python::{check_module, Target};

const SOURCE: &str = include_str!("../examples/core/reverse.py");

#[test]
fn reverse_get_is_checked_generically_and_normalizes_to_reflexivity() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let module = check_module(SOURCE, target).unwrap();
        let e = module.elaborator;
        let nat = |n| (0..n).fold(E::Zero, |n, _| n.succ());
        for len in 1..=4 {
            let xs = (0..len).rev().fold(E::vnil(E::Nat), |xs, i| {
                E::vcons(E::Nat, nat(len - i - 1), nat(i + 10), xs)
            });
            for index in 0..len {
                let i = (0..index).fold(E::fz(nat(len - index - 1)), |i, j| {
                    E::fs(nat(len - index + j), i)
                });
                let proof = e
                    .infer(&E::name("reverse_get").app(nat(len)).app(xs.clone()).app(i))
                    .unwrap();
                let expected = e.infer(&nat(index + 10).refl()).unwrap();
                assert_eq!(e.kernel().normalize(&proof.term).unwrap(), expected.term);
            }
        }
    }
}

#[test]
fn reverse_get_rejects_incorrect_proofs_and_indices() {
    for bad in [
        SOURCE.replace("mirror(n, i)), get(n, xs, i)", "i), get(n, xs, i)"),
        SOURCE.replace(
            "return get_snoc_last(k, x, reverse(k, rest))",
            "return refl(x)",
        ),
        SOURCE.replace("reverse_get(k, rest, j),", "reverse_get(k, rest, i),"),
        SOURCE.replace(
            "get_snoc_weaken(k, x, reverse(k, rest), mirror(k, j)),",
            "refl(x),",
        ),
    ] {
        assert!(check_module(&bad, Target::Python314).is_err());
    }
}

#[test]
fn transitivity_rejects_disconnected_equalities() {
    let source = "from deppy import dependent, Nat, Eq, refl, trans\n@dependent\ndef bad(n: Nat) -> Eq[Nat, 0, 1]:\n    return trans(refl(0), refl(1))\n";
    assert!(check_module(source, Target::Python314).is_err());
}
