use deppy_python::Target;
use deppy_runtime::{compile_module, compile_module_with_resolver};

const TARGET: Target = Target::Python314;
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, axiom, Nat, Eq, refl, J, Pi, ann\n";

fn source(body: &str) -> String {
    format!("{HEADER}{body}")
}

#[test]
fn axioms_never_become_runtime_stubs() {
    let error =
        compile_module(&source("@axiom\ndef assumed() -> Nat:\n    ...\n"), TARGET).unwrap_err();
    assert!(error.message.contains("no runtime implementation"));
}

#[test]
fn discarded_axiomatic_proofs_cannot_leak_into_runtime_j() {
    let library = source(
        "@axiom\ndef assumed() -> Eq[Nat, 0, 0]:\n    ...\n@dependent\ndef proof() -> Eq[Nat, 0, 0]:\n    return assumed()\n",
    );
    for expression in [
        "proof()",
        "ann(lambda f: f(0), Pi[Pi[Nat, lambda n: Eq[Nat, 0, 0]], lambda f: Eq[Nat, 0, 0]])(lambda n: proof())",
    ] {
        let main = source(&format!(
            "from assumptions import proof\n@dependent\ndef bad() -> Nat:\n    return J(0, Nat, 0, lambda end, p: Nat, 0, 0, {expression})\n"
        ));
        let mut resolver = |_: &str| Ok(Some(library.clone()));
        let error = compile_module_with_resolver(&main, TARGET, &mut resolver).unwrap_err();
        assert!(error.message.contains("no runtime implementation"));
    }
    let bad = source(
        "@dependent\ndef bad[p: Eq[Nat, 0, 0]]() -> Nat:\n    return J(0, Nat, 0, lambda end, q: Nat, 0, 0, p)\n",
    );
    let error = compile_module(&bad, TARGET).unwrap_err();
    assert!(error.message.contains("erased variable"));
}
