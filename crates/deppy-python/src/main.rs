use deppy_python::{check_module, Target};
fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 1 {
        eprintln!("usage: deppy-python FILE.py (Python 3.14 syntax; static checking only)");
        return std::process::ExitCode::from(2);
    }
    let path = std::path::Path::new(&args[0]);
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            return std::process::ExitCode::FAILURE;
        }
    };
    match check_module(&source, Target::Python314) {
        Ok(module) => {
            for (name, _, _) in &module.definitions {
                println!("checked {name}");
            }
            println!("{} dependent definitions checked; ordinary Python and runtime erasure are not checked", module.definitions.len());
            std::process::ExitCode::SUCCESS
        }
        Err(e) => {
            let prefix = &source[..e.span.start];
            let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
            let column = prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1;
            eprintln!("{}:{line}:{column}: {}", path.display(), e.message);
            std::process::ExitCode::FAILURE
        }
    }
}
