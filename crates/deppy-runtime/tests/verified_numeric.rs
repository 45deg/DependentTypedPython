use deppy_python::Target;
use deppy_runtime::compile_exports_with_resolver;
use std::{
    io::Write,
    process::{Command, Stdio},
};

const SOURCE: &str = include_str!("../../deppy-python/examples/verified/verified_numeric.py");
const PROOF: &str = include_str!("../../deppy-python/examples/verified/gcd_proof.py");
const EXPORTS: &[&str] = &[
    "subtract",
    "gcd",
    "lift",
    "negate",
    "signed_div",
    "signed_mod",
];

fn compile(source: &str, exports: &[&str]) -> Result<String, deppy_python::Diagnostic> {
    compile_exports_with_resolver(
        source,
        Target::Python314,
        &mut |name: &str| Ok((name == "gcd_proof").then(|| PROOF.to_owned())),
        exports,
    )
}

#[test]
fn checked_numeric_example_executes_with_default_budgets() {
    let generated = compile(SOURCE, EXPORTS).unwrap();
    let mut child = Command::new("python3")
        .args(["-I", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Python 3 is required for runtime integration tests");
    let mut input = child.stdin.take().unwrap();
    input.write_all(generated.as_bytes()).unwrap();
    input
        .write_all(
            br#"
import math
assert set(exports) == {'subtract', 'gcd', 'lift', 'negate', 'signed_div', 'signed_mod'}
checks = 0
for a in range(10):
    for b in range(10):
        assert exports['subtract'](a, b) == max(a - b, 0), (a, b)
        assert exports['gcd'](a, b) == math.gcd(a, b), (a, b)
        checks += 2

# Int has a nominal constructor representation, not a Python int boundary.
# Construct every input through checked exports, including canonical zero.
def integer(n):
    return exports['lift'](n) if n >= 0 else exports['negate'](exports['lift'](-n))

for a in range(-8, 9):
    assert exports['negate'](integer(a)) == integer(-a), a
    checks += 1
    for b in range(-4, 5):
        q, r = (a // b, a % b) if b else (0, 0)
        assert exports['signed_div'](integer(a), integer(b)) == integer(q), (a, b)
        assert exports['signed_mod'](integer(a), integer(b)) == integer(r), (a, b)
        checks += 2

def rejected(name, *args):
    try:
        exports[name](*args)
    except TypeError:
        return
    raise AssertionError((name, args))

rejected('lift', -1)
rejected('gcd', True, 1)
rejected('subtract', 1, -1)
rejected('signed_div', 1, 2)
rejected('negate', (object(), 0, (1,)))
print(f'{checks} numeric comparisons passed')
"#,
        )
        .unwrap();
    drop(input);
    let result = child.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("523 numeric comparisons passed"));
}

#[test]
fn selecting_exports_does_not_bypass_module_proofs() {
    // The invalid GCD is not exported, but its obligations must still be checked.
    let invalid = SOURCE.replace("x, y = y, x % y", "x, y = y, 0");
    assert!(compile(&invalid, &["lift"]).is_err());
    let error = compile(SOURCE, &["missing"]).unwrap_err();
    assert!(error.message.contains("unknown runtime export missing"));
}
