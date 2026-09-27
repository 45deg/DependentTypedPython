use deppy_python::{check_module_with_resolver, Target};

const EXAMPLE: &str = include_str!("../examples/verified/verified_numeric.py");
const PROOF: &str = include_str!("../examples/verified/gcd_proof.py");

fn check(source: &str) -> Result<deppy_python::CheckedModule, deppy_python::Diagnostic> {
    check_module_with_resolver(source, Target::Python314, &mut |name: &str| {
        Ok((name == "gcd_proof").then(|| PROOF.to_owned()))
    })
}

#[test]
fn euclid_is_a_greatest_common_divisor_for_all_naturals() {
    let checked = check(EXAMPLE).unwrap_or_else(|error| panic!("{error}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    assert!(checked.interface.exports()["gcd"].verified_spec.is_some());
    assert!(checked.interface.exports().contains_key("gcd_correct"));

    for changed in [
        EXAMPLE.replace("    return x\n", "    return 0\n"),
        EXAMPLE.replace("x, y = y, x % y", "x, y = y, 0"),
    ] {
        assert!(check(&changed).is_err(), "incorrect Euclid variant passed");
    }
}
