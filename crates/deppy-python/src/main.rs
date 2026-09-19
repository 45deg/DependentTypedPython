use deppy_python::{
    check_module_with_resolver, compile_module_with_resolver, FileResolver, Target,
};
fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let emit = args.len() == 2 && args[0] == "--emit-python";
    if args.len() != 1 && !emit {
        eprintln!("usage: deppy-python [--emit-python] FILE.py (Python 3.14 input syntax)");
        return std::process::ExitCode::from(2);
    }
    let path = std::path::Path::new(&args[usize::from(emit)]);
    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            return std::process::ExitCode::FAILURE;
        }
    };
    let mut resolver = match FileResolver::new(
        path.parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(std::path::Path::new(".")),
    ) {
        Ok(resolver) => resolver,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            return std::process::ExitCode::FAILURE;
        }
    };
    if emit {
        return match compile_module_with_resolver(&source, Target::Python314, &mut resolver) {
            Ok(code) => {
                print!("{code}");
                std::process::ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("{}: {e}", path.display());
                std::process::ExitCode::FAILURE
            }
        };
    }
    match check_module_with_resolver(&source, Target::Python314, &mut resolver) {
        Ok(module) => {
            for (name, _, _) in &module.definitions {
                let assumptions = &module.axiom_dependencies[name];
                if assumptions.is_empty() {
                    println!("checked {name} [axiom-free]");
                } else {
                    println!("checked {name} [axioms: {}]", assumptions.join(", "));
                }
            }
            println!("{} dependent declarations checked; ordinary Python and runtime erasure are not checked", module.definitions.len());
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
