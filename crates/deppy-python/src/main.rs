use deppy_core::{standard::NAT, DataOp, Term};
use deppy_elab::Expr;
use deppy_python::{analyze_module_with_options_and_resolver, FileResolver, FrontendOptions};

fn display_result(term: &Term) -> String {
    let mut value = term;
    let mut count = 0usize;
    while let Term::Data {
        op: DataOp::Constructor(id, 1),
        arguments,
    } = value
    {
        if *id != NAT || arguments.len() != 1 {
            break;
        }
        count += 1;
        value = &arguments[0];
    }
    if matches!(value, Term::Data { op: DataOp::Constructor(id, 0), arguments } if *id == NAT && arguments.is_empty())
    {
        return count.to_string();
    }
    match term {
        Term::Refl { value, .. } => format!("refl({})", display_result(value)),
        _ => format!("{term:?}"),
    }
}

fn main() -> std::process::ExitCode {
    let mut goals = false;
    let mut json = false;
    let mut options = FrontendOptions::default();
    let mut args = Vec::new();
    let mut input = std::env::args_os().skip(1).peekable();
    let eval = input.next_if(|arg| arg == "eval").is_some();
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
    if (!eval && args.len() != 1) || (eval && args.len() < 2) || (eval && (goals || json)) {
        eprintln!("usage: deppy-python [--goals] [--json] [--elaboration-steps N] FILE.py\n       deppy-python eval [--elaboration-steps N] FILE.py NAME [NAT ...] (Python 3.14 input syntax)");
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
    if let (true, Some(module)) = (eval, analysis.checked.as_ref()) {
        let name = match args[1].to_str() {
            Some(name) => name,
            None => {
                eprintln!("NAME must be UTF-8");
                return std::process::ExitCode::from(2);
            }
        };
        if module.elaborator.definition_id(name).is_none() {
            eprintln!("unknown checked name: {name}");
            return std::process::ExitCode::from(2);
        }
        let mut expression = Expr::name(name);
        for arg in &args[2..] {
            let Some(n) = arg.to_str().and_then(|value| value.parse::<usize>().ok()) else {
                eprintln!(
                    "arguments must be natural numbers: {}",
                    arg.to_string_lossy()
                );
                return std::process::ExitCode::from(2);
            };
            let mut nat = Expr::Zero;
            for _ in 0..n {
                nat = nat.succ();
            }
            expression = expression.app(nat);
        }
        let result = module.elaborator.infer(&expression).and_then(|checked| {
            module
                .elaborator
                .kernel()
                .normalize(&checked.term)
                .map_err(Into::into)
        });
        return match result {
            Ok(term) => {
                println!("{}", display_result(&term));
                std::process::ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("{error}");
                std::process::ExitCode::FAILURE
            }
        };
    }
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
