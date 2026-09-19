use deppy_core::RuntimeTerm;
use deppy_python::{check_module, Diagnostic, Span, Target};

/// Generate a standalone Python module from kernel-checked runtime IR.
/// The generated declarations are curried internally and exposed as ordinary
/// positional functions. Ordinary source Python is deliberately excluded.
pub fn compile_module(source: &str, target: Target) -> Result<String, Diagnostic> {
    compile_checked(check_module(source, target)?)
}

pub fn compile_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl deppy_python::SourceResolver,
) -> Result<String, Diagnostic> {
    compile_checked(deppy_python::check_module_with_resolver(
        source, target, resolver,
    )?)
}

fn compile_checked(checked: deppy_python::CheckedModule) -> Result<String, Diagnostic> {
    let kernel = checked.elaborator.kernel();
    let definitions = kernel.erase_definitions().map_err(|e| Diagnostic {
        span: Span { start: 0, end: 0 },
        message: e.to_string(),
    })?;
    let mut out = include_str!("runtime.py").to_owned();
    for (id, term) in definitions {
        out.push_str(&format!("\n_d{id} = {}\n", expression(&term, &[])));
    }
    out.push_str("\n# Public checked declarations (implicit parameters are erased).\n");
    // A dictionary avoids collisions between source identifiers and runtime helpers.
    out.push_str("exports = {}\n");
    for (name, public_id, span) in checked.definitions {
        let id = checked
            .constructors
            .iter()
            .find(|(n, _, _)| n == &name)
            .map_or(public_id, |(_, id, _)| *id);
        if kernel
            .definition(id)
            .map_err(|e| Diagnostic {
                span,
                message: e.to_string(),
            })?
            .body
            .is_none()
        {
            return Err(Diagnostic {
                span,
                message: format!("axiom {name} has no runtime implementation"),
            });
        }
        let signature = kernel
            .runtime_signature(&deppy_core::Term::Global(id).arc())
            .map_err(|e| Diagnostic {
                span,
                message: format!("runtime boundary for {name}: {e}"),
            })?;
        let args: Vec<_> = (0..signature.arguments.len())
            .map(|i| format!("a{i}"))
            .collect();
        out.push_str(&format!("def _export{id}({}):\n", args.join(", ")));
        for (i, ty) in signature.arguments.iter().enumerate() {
            out.push_str(&format!(
                "    a{i} = _validate(a{i}, {})\n",
                schema(ty, &args[..i])
            ));
        }
        let mut call = format!("_d{id}");
        for arg in &args {
            call.push_str(&format!("({arg})"));
        }
        out.push_str(&format!(
            "    return _validate({call}, {}, True)\n",
            schema(&signature.result, &args)
        ));
        out.push_str(&format!("exports[{}] = _export{id}\n", py_string(&name)));
    }
    Ok(out)
}
fn py_string(s: &str) -> String {
    // Names cannot contain controls or quotes, but encode rather than rely on that.
    format!(
        "'{}'",
        s.chars()
            .map(|c| format!("\\U{:08x}", c as u32))
            .collect::<String>()
    )
}
fn expression(term: &RuntimeTerm, env: &[String]) -> String {
    // Large source integer literals become successor chains in core. Emit them
    // as literals to avoid CPython's parser nesting limit.
    let mut natural = term;
    let mut count = 0usize;
    while let RuntimeTerm::Prim("succ", args) = natural {
        if args.len() != 1 {
            break;
        }
        count += 1;
        natural = &args[0];
    }
    if matches!(natural, RuntimeTerm::Prim("zero", args) if args.is_empty()) {
        return count.to_string();
    }
    let sub = |t| expression(t, env);
    match term {
        RuntimeTerm::Unit => "None".into(),
        RuntimeTerm::Var(i) => env[env.len() - i - 1].clone(),
        RuntimeTerm::Global(id) => format!("_d{id}"),
        RuntimeTerm::Lam(body) => {
            let name = format!("v{}", env.len());
            let mut next = env.to_vec();
            next.push(name.clone());
            format!("(lambda {name}: {})", expression(body, &next))
        }
        RuntimeTerm::App(f, a) => format!("({})({})", sub(f), sub(a)),
        RuntimeTerm::Let(value, body) => {
            let name = format!("v{}", env.len());
            let mut next = env.to_vec();
            next.push(name.clone());
            format!(
                "(lambda {name}: {})({})",
                expression(body, &next),
                sub(value)
            )
        }
        RuntimeTerm::Prim(name, args) => format!(
            "_{name}({})",
            args.iter().map(sub).collect::<Vec<_>>().join(", ")
        ),
        RuntimeTerm::Record(id, fields) => format!(
            "_record({id}, ({}))",
            fields
                .iter()
                .map(|t| format!("{},", sub(t)))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        RuntimeTerm::RecordElim(id, branch, value) => {
            format!("_record_elim({id}, {}, {})", sub(branch), sub(value))
        }
    }
}

fn schema(ty: &deppy_core::RuntimeType, env: &[String]) -> String {
    use deppy_core::RuntimeType as T;
    match ty {
        T::Opaque => "('opaque',)".into(),
        T::Type => "('type',)".into(),
        T::Nat => "('nat',)".into(),
        T::Proof => "('proof',)".into(),
        T::Vec(element, len) => format!(
            "('vec', {}, {})",
            schema(element, env),
            expression(len, env)
        ),
        T::Fin(bound) => format!("('fin', {})", expression(bound, env)),
        T::Pair(first, second) => {
            let name = format!("s{}", env.len());
            let mut next = env.to_vec();
            next.push(name.clone());
            format!(
                "('pair', {}, lambda {name}: {})",
                schema(first, env),
                schema(second, &next)
            )
        }
        T::Record(id, fields) => {
            let mut next = env.to_vec();
            let mut names = vec![];
            let mut validators = vec![];
            for field in fields {
                validators.push(format!(
                    "(lambda {}: {}),",
                    names.join(", "),
                    schema(field, &next)
                ));
                let name = format!("s{}", next.len());
                names.push(name.clone());
                next.push(name);
            }
            format!("('record', _tag({id}), ({}))", validators.join(" "))
        }
    }
}
