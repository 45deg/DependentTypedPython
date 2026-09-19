use deppy_python::{analyze_module_with_options_and_resolver, FileResolver, FrontendOptions};
fn main() -> std::process::ExitCode {
    let mut goals = false;
    let mut json = false;
    let mut options = FrontendOptions::default();
    let mut args = Vec::new();
    let mut input = std::env::args_os().skip(1);
    while let Some(arg) = input.next() {
        if arg == "--goals" {
            goals = true;
        } else if arg == "--json" {
            json = true;
        } else if arg == "--elaboration-steps" {
            let steps = input
                .next()
                .and_then(|value| value.to_str().and_then(|s| s.parse::<usize>().ok()))
                .filter(|steps| *steps > 0);
            let Some(steps) = steps else {
                eprintln!("--elaboration-steps requires a positive integer");
                return std::process::ExitCode::from(2);
            };
            options.elaboration_steps = steps;
        } else {
            args.push(arg);
        }
    }
    if args.len() != 1 {
        eprintln!("usage: deppy-python [--goals] [--json] [--elaboration-steps N] FILE.py (Python 3.14 input syntax)");
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
    let mut analysis = analyze_module_with_options_and_resolver(&source, options, &mut resolver);
    analysis.set_root_source_name(&path.display().to_string());
    if json {
        println!("{}", analysis.to_json());
        return if analysis.checked.is_some() {
            std::process::ExitCode::SUCCESS
        } else {
            std::process::ExitCode::FAILURE
        };
    }
    if goals {
        for goal in &analysis.goals {
            println!("goal {}: {}", goal.id, goal.name);
            if let Some(location) = &goal.location {
                println!(
                    "  source {} bytes {}..{}",
                    location.source, location.start, location.end
                );
            }
            for local in &goal.context {
                println!(
                    "  {}: {}{}",
                    local.name,
                    local.ty,
                    local
                        .value
                        .as_ref()
                        .map(|v| format!(" = {v}"))
                        .unwrap_or_default()
                );
            }
            println!("  ⊢ {}", goal.expected);
        }
    }
    if let Some(module) = analysis.checked {
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
    } else {
        for e in analysis.diagnostics {
            let prefix = source.get(..e.span.start).unwrap_or("");
            let line = e
                .details
                .line
                .unwrap_or_else(|| prefix.bytes().filter(|b| *b == b'\n').count() + 1);
            let column = e
                .details
                .column
                .unwrap_or_else(|| prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1);
            let origin = e
                .details
                .source
                .as_deref()
                .filter(|s| !s.is_empty())
                .map(str::to_owned)
                .unwrap_or_else(|| path.display().to_string());
            eprintln!("{origin}:{line}:{column}: {}", e.message);
        }
        std::process::ExitCode::FAILURE
    }
}
