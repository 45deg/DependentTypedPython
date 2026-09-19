use std::{fs, process::Command};

#[test]
fn cli_resolves_local_modules_and_emits_working_code() {
    let root = std::env::temp_dir().join(format!("deppy-runtime-cli-{}", std::process::id()));
    fs::create_dir_all(root.join("proofs")).unwrap();
    fs::write(
        root.join("proofs/__init__.py"),
        "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\n@dependent\ndef identity(n: Nat) -> Nat:\n    return n\n@dependent\ndef proof(n: Nat) -> Eq[Nat, n, n]:\n    return refl(n)\n",
    )
    .unwrap();
    let main = root.join("main.py");
    fs::write(&main, "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq\nfrom proofs import identity, proof\n@dependent\ndef run(n: Nat) -> Nat:\n    return identity(n)\n@dependent\ndef verify(n: Nat) -> Eq[Nat, n, n]:\n    return proof(n)\n").unwrap();
    let compiled = Command::new(env!("CARGO_BIN_EXE_deppy-runtime"))
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
    fs::remove_dir_all(root).unwrap();
}
