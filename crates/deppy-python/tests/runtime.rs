use deppy_python::{compile_module, Target};
use std::{
    io::Write,
    process::{Command, Stdio},
};
fn run(source: &str, assertions: &str) {
    let generated = compile_module(source, Target::Python314).unwrap();
    let mut child = Command::new("python3")
        .arg("-I")
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Python 3 is required for runtime integration tests");
    let mut input = child.stdin.take().unwrap();
    input.write_all(generated.as_bytes()).unwrap();
    input.write_all(assertions.as_bytes()).unwrap();
    drop(input);
    let result = child.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}
#[test]
fn get_and_zero_right_execute() {
    run(include_str!("../examples/proofs.py"), "\nfor n in range(1, 9):\n    xs = tuple(range(n))\n    for i in range(n):\n        assert exports['get'](n, xs, (n, i)) == i\nfor n in range(9):\n    assert exports['zero_right'](n) is None\n");
}
#[test]
fn dependent_record_round_trip_executes() {
    run(include_str!("../examples/records.py"), "\nfor n in range(9):\n    xs = tuple(range(n))\n    p = exports['pack'](n, xs)\n    r = exports['as_record'](p)\n    assert exports['as_pair'](r) == p\n");
}
#[test]
fn pre_match_definitions_execute() {
    run(include_str!("../examples/before_match.py"), "\nfor n in range(9):\n    assert exports['count'](n) == n\n    assert exports['keep'](n, tuple(range(n))) == tuple(range(n))\n    assert exports['reflexive'](n) is None\n");
}
#[test]
fn erased_runtime_use_is_rejected_by_compiler() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Type, Nat, Vec\n@dependent\ndef bad[T: Type, n: Nat](xs: Vec[T, n]) -> Nat:\n    return n\n";
    assert!(compile_module(source, Target::Python314)
        .unwrap_err()
        .message
        .contains("erased variable"));
}

#[test]
fn boundaries_reject_forged_indices_mutation_and_nominal_confusion() {
    run(
        include_str!("../examples/proofs.py"),
        r#"
def rejected(f, *args):
    try:
        f(*args)
    except TypeError:
        return
    raise AssertionError('invalid boundary data accepted')
get = exports['get']
for args in [(2, (1,), (2, 0)), (1, (1,), (2, 0)), (1, (1,), (1, 1)),
             (0, (), (0, 0)), (True, (1,), (1, 0)), (1, [1], (1, 0)),
             (1, ([1],), (1, 0)), (1, (1,), (1, False))]:
    rejected(get, *args)
rejected(exports['zero_right'], -1)
"#,
    );
    run(
        include_str!("../examples/records.py"),
        r#"
r = exports['SomeVec'](2, (10, 20))
assert exports['as_pair'](r) == (2, (10, 20))
for bad in [(object(), r[1]), (r[0], (2, (10,))), (r[0], [2, (10, 20)])]:
    try:
        exports['as_pair'](bad)
    except TypeError:
        pass
    else:
        raise AssertionError('forged record accepted')
"#,
    );
}
#[test]
fn identity_append_and_natural_recursors_execute() {
    run(include_str!("../examples/basics.py"), "\nassert exports['identity']((1, 'x')) == (1, 'x')\nassert exports['twice'](9) == 11\nassert exports['empty'](4) == ()\n");
    run(
        include_str!("../examples/structural.py"),
        r#"
for n in range(6):
    for m in range(6):
        xs, ys = tuple(range(n)), tuple(range(m))
        assert exports['append'](n, m, xs, ys) == xs + ys
assert exports['add'](128, 3) == 131
"#,
    );
}
#[test]
fn unchecked_source_is_never_emitted_or_executed() {
    run("from __future__ import annotations\nfrom deppy import dependent, Nat\ndef unchecked():\n    raise RuntimeError('must not run')\n@dependent\ndef safe(n: Nat) -> Nat:\n    return n\nassert False\n", "\nassert list(exports) == ['safe']\nassert exports['safe'](3) == 3\n");
}

#[test]
fn fin_recursion_and_equality_transport_execute() {
    run(r#"from __future__ import annotations
from deppy import dependent, Nat, Z, S, Fin, FZ, FS
@dependent(decreases="i")
def rank(n: Nat, i: Fin[n]) -> Nat:
    match i:
        case FZ(k):
            return Z()
        case FS(k, j):
            return S(rank(k, j))
"#, "\nfor n in range(1, 9):\n    for i in range(n):\n        assert exports['rank'](n, (n, i)) == i\n");
    // zero_right exercises J via cong; proof arguments from Python are rejected.
    run(r#"from __future__ import annotations
from deppy import dependent, Nat, Eq
@dependent
def use_proof(n: Nat, p: Eq[Nat, n, n]) -> Nat:
    return n
"#, "\ntry:\n    exports['use_proof'](3, _PROOF)\nexcept TypeError:\n    pass\nelse:\n    raise AssertionError('external proof accepted')\n");
}

#[test]
fn unsupported_boundaries_report_a_compile_error() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Type, Nat, Vec\n@dependent\ndef keep[T: Type, n: Nat](xs: Vec[T, n]) -> Vec[T, n]:\n    return xs\n";
    assert!(compile_module(source, Target::Python314)
        .unwrap_err()
        .message
        .contains("runtime boundary"));
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Pi\n@dependent\ndef apply(f: Pi[Nat, lambda n: Nat], n: Nat) -> Nat:\n    return f(n)\n";
    assert!(compile_module(source, Target::Python314)
        .unwrap_err()
        .message
        .contains("unsupported"));
}

#[test]
fn concrete_vector_carriers_and_large_literals_are_checked() {
    // The core uses recursive Rust traversals; reserve enough stack for this
    // parser-depth regression, independently of the default test thread stack.
    std::thread::Builder::new().stack_size(16 * 1024 * 1024).spawn(|| {
    run("from __future__ import annotations\nfrom deppy import dependent, Nat, Vec\n@dependent\ndef keep(n: Nat, xs: Vec[Nat, n]) -> Vec[Nat, n]:\n    return xs\n@dependent\ndef literal(n: Nat) -> Nat:\n    return 256\n", r#"
assert exports['literal'](0) == 256
assert exports['keep'](2, (0, 1)) == (0, 1)
for xs in [(-1,), (True,), ('x',)]:
    try:
        exports['keep'](1, xs)
    except TypeError:
        pass
    else:
        raise AssertionError('invalid Nat element accepted')
"#);
    }).unwrap().join().unwrap();
}
