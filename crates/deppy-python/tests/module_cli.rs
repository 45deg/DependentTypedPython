use std::{fs, process::Command};

#[test]
fn cli_accepts_an_elaboration_budget_and_rejects_invalid_values() {
    let root = std::env::temp_dir().join(format!("deppy-budget-cli-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("proof.py");
    fs::write(
        &path,
        "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\n@dependent\ndef proof(n: Nat) -> Eq[Nat, n, n]:\n    return refl(n)\n",
    )
    .unwrap();
    let run = |steps: &str| {
        Command::new(env!("CARGO_BIN_EXE_deppy-python"))
            .args(["--elaboration-steps", steps])
            .arg(&path)
            .output()
            .unwrap()
    };
    let accepted = run("10000000");
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr)
    );
    let exhausted = run("1");
    assert!(!exhausted.status.success());
    assert!(String::from_utf8_lossy(&exhausted.stderr).contains("budget exhausted"));
    for invalid in ["0", "-1", "no", "999999999999999999999999999999"] {
        let output = run(invalid);
        assert_eq!(output.status.code(), Some(2));
        assert!(String::from_utf8_lossy(&output.stderr).contains("positive integer"));
    }
    let missing = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg("--elaboration-steps")
        .output()
        .unwrap();
    assert_eq!(missing.status.code(), Some(2));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn cli_resolves_local_modules_without_executing_python() {
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
    assert!(String::from_utf8_lossy(&failed.stderr).contains("proofs/__init__.py:7:12:"));
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

#[test]
fn goal_cli_reports_unfinished_proofs_without_claiming_success() {
    let root = std::env::temp_dir().join(format!("deppy-goals-cli-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let path = root.join("goals.py");
    fs::write(&path, "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, hole\n@dependent\ndef identity(n: Nat) -> Eq[Nat, n, n]:\n    return hole('identity')\n").unwrap();
    let text = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg("--goals")
        .arg(&path)
        .output()
        .unwrap();
    assert!(!text.status.success());
    let stdout = String::from_utf8_lossy(&text.stdout);
    assert!(stdout.contains("n: Nat"));
    assert!(stdout.contains("⊢ Eq[Nat, n, n]"));
    assert!(!stdout.contains("checked identity"));
    let json = Command::new(env!("CARGO_BIN_EXE_deppy-python"))
        .arg("--json")
        .arg(&path)
        .output()
        .unwrap();
    assert!(!json.status.success());
    let stdout = String::from_utf8_lossy(&json.stdout);
    assert!(stdout.starts_with("{\"checked\":false,"));
    assert!(stdout.contains("\"name\":\"identity\""));
    assert!(stdout.contains("\"expected\":\"Eq[Nat, n, n]\""));
    fs::remove_dir_all(root).unwrap();
}
