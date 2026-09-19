use deppy_python::{FileResolver, Target};
use deppy_runtime::compile_module_with_resolver;

fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 1 {
        eprintln!("usage: deppy-runtime FILE.py (Python 3.14 input syntax)");
        return std::process::ExitCode::from(2);
    }
    let path = std::path::Path::new(&args[0]);
    let source = match std::fs::read_to_string(path) {
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
    match compile_module_with_resolver(&source, Target::Python314, &mut resolver) {
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
