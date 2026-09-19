use std::{fs, process::Command};

#[test]
fn cli_resolves_local_modules_without_executing_python_and_emits_working_code() {
    let root = std::env::temp_dir().join(format!("deppy-library-cli-{}", std::process::id()));
    fs::create_dir_all(root.join("proofs")).unwrap();
    let library = r#"from __future__ import annotations
from deppy import dependent, Nat, Eq, refl
from deppy.equality import trans
assert False, 'ordinary Python must never execute during checking'
@dependent
def identity(n: Nat) -> Nat:
    return n
@dependent
def proof(n: Nat) -> Eq[Nat, n, n]:
    return trans(refl(n), refl(n))
"#;
    fs::write(root.join("proofs/__init__.py"), library).unwrap();
    let main = root.join("main.py");
    fs::write(&main, "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq\nfrom proofs import identity, proof\n@dependent\ndef run(n: Nat) -> Nat:\n    return identity(n)\n@dependent\ndef verify(n: Nat) -> Eq[Nat, n, n]:\n    return proof(n)\n").unwrap();
    let checked = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg(&main)
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
    assert!(String::from_utf8_lossy(&checked.stdout).contains("checked verify [axiom-free]"));
    let compiled = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg("--emit-python")
        .arg(&main)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let mut code = String::from_utf8(compiled.stdout).unwrap();
    code.push_str("\nassert exports['run'](9) == 9\nassert exports['verify'](9) is None\nassert set(exports) == {'run', 'verify'}\n");
    let executable = root.join("generated.py");
    fs::write(&executable, code).unwrap();
    let result = Command::new("python3")
        .arg("-I")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    fs::write(
        root.join("proofs/__init__.py"),
        library.replace("return n", "return Nat"),
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg(&main)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(String::from_utf8_lossy(&failed.stderr).contains("in proofs"));
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn source_resolver_rejects_a_symlink_outside_its_root() {
    use deppy_python::{FileResolver, SourceResolver};
    let base = std::env::temp_dir().join(format!("deppy-library-symlink-{}", std::process::id()));
    fs::create_dir_all(base.join("root")).unwrap();
    fs::write(base.join("outside.py"), "").unwrap();
    std::os::unix::fs::symlink(base.join("outside.py"), base.join("root/escape.py")).unwrap();
    let mut resolver = FileResolver::new(base.join("root")).unwrap();
    assert!(resolver
        .source("escape")
        .unwrap_err()
        .contains("escapes source root"));
    assert!(resolver.source("../outside").is_err());
    assert!(resolver.source("missing").unwrap().is_none());
    fs::remove_dir_all(base).unwrap();
}
