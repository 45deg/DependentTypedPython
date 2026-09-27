use deppy_python::{FileResolver, Target};
use deppy_runtime::{compile_exports_with_resolver, compile_module_with_resolver};

fn main() -> std::process::ExitCode {
    let usage = || {
        eprintln!("usage: deppy-runtime [--export NAME ...] FILE.py (Python 3.14 input syntax)");
        std::process::ExitCode::from(2)
    };
    let mut args = std::env::args_os().skip(1);
    let mut exports = vec![];
    let mut path = None;
    while let Some(arg) = args.next() {
        if arg == "--export" {
            let Some(name) = args.next().and_then(|name| name.into_string().ok()) else {
                return usage();
            };
            if name.is_empty() || name.starts_with('-') {
                return usage();
            }
            exports.push(name);
        } else if arg.to_string_lossy().starts_with('-') || path.is_some() {
            return usage();
        } else {
            path = Some(std::path::PathBuf::from(arg));
        }
    }
    let Some(path) = path else {
        return usage();
    };
    let source = match std::fs::read_to_string(&path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            return std::process::ExitCode::FAILURE;
        }
    };
    let mut resolver = match FileResolver::new(
        path.parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or(std::path::Path::new(".")),
    ) {
        Ok(resolver) => resolver,
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            return std::process::ExitCode::FAILURE;
        }
    };
    let compiled = if exports.is_empty() {
        compile_module_with_resolver(&source, Target::Python314, &mut resolver)
    } else {
        let names: Vec<_> = exports.iter().map(String::as_str).collect();
        compile_exports_with_resolver(&source, Target::Python314, &mut resolver, &names)
    };
    match compiled {
        Ok(code) => {
            print!("{code}");
            std::process::ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{}: {error}", path.display());
            std::process::ExitCode::FAILURE
        }
    }
}
