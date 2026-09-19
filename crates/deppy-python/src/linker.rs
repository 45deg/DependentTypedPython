//! Kernel-check lowered declarations before exposing a module interface.
use crate::*;

pub(crate) fn check_lowered(
    module: Module,
    options: FrontendOptions,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<CheckedModule, Diagnostic> {
    // Dependent Fin motives and composed equality proofs (e.g. reverse_get)
    // exceed the small elaborator default. Keep checking explicitly bounded.
    let mut elaborator = Elaborator::new(options.elaboration_steps);
    let mut definitions = vec![];
    let mut record_id = 0;
    let mut data_id = 0;
    let mut data_entries = std::collections::BTreeMap::new();
    let mut constructors = vec![];
    let mut axiom_names = std::collections::HashMap::new();
    for d in module.declarations {
        let diagnostic = |message: String| {
            let origin = module
                .origins
                .get(&d.name)
                .map(String::as_str)
                .unwrap_or("");
            Diagnostic {
                details: Default::default(),
                span: d.span,
                message,
            }
            .in_source(
                origin,
                module.sources.get(origin).map(String::as_str).unwrap_or(""),
            )
        };
        let elab_diagnostic = |error: deppy_elab::Error| {
            let location = match &error {
                deppy_elab::Error::Located { location, .. } => Some(location),
                deppy_elab::Error::Goals(goals) => {
                    goals.first().and_then(|goal| goal.location.as_ref())
                }
                _ => None,
            };
            let mut result = if let Some(location) = location {
                Diagnostic {
                    details: Default::default(),
                    span: Span {
                        start: location.start,
                        end: location.end,
                    },
                    message: error.to_string(),
                }
                .in_source(
                    &location.source,
                    module
                        .sources
                        .get(&location.source)
                        .map(String::as_str)
                        .unwrap_or(""),
                )
            } else {
                diagnostic(error.to_string())
            };
            if let Some(source) = &result.details.source {
                if let Some(display) = module.source_names.get(source) {
                    result.details.source = Some(display.clone());
                }
            }
            result.details.kind = if matches!(error.cause(), deppy_elab::Error::Kernel(_)) {
                DiagnosticKind::Kernel
            } else {
                DiagnosticKind::Elaboration
            };
            if result.span != d.span {
                result.details.related.push(deppy_elab::SourceLocation {
                    source: result.details.source.clone().unwrap_or_default(),
                    start: d.span.start,
                    end: d.span.end,
                });
            }
            if let Some((expected, actual)) = error.type_details() {
                result.details.expected = Some(expected.to_owned());
                result.details.actual = Some(actual.to_owned());
            }
            if let deppy_elab::Error::Goals(goals) = error.cause() {
                result.details.goals = goals.clone();
                for goal in &mut result.details.goals {
                    if let Some(location) = &mut goal.location {
                        if let Some(display) = module.source_names.get(&location.source) {
                            location.source = display.clone();
                        }
                    }
                }
            }
            result
        };
        if let DeclarationBody::Data(decl) = &d.body {
            let exports = elaborator
                .declare_data(data_id, decl.clone())
                .map_err(elab_diagnostic)?;
            for (index, (name, _)) in exports.iter().enumerate() {
                data_entries.insert(name.clone(), (data_id, index.checked_sub(1)));
            }
            data_id += 1;
            for (name, id) in exports {
                if module.public_names.contains(&name) {
                    definitions.push((name, id, d.span));
                }
            }
            continue;
        }
        if matches!(d.body, DeclarationBody::Axiom) {
            let id = elaborator
                .declare_axiom(&d.name, &d.ty)
                .map_err(elab_diagnostic)?;
            axiom_names.insert(id, d.name.clone());
            if module.public_names.contains(&d.name) {
                definitions.push((d.name, id, d.span));
            }
            continue;
        }
        if let DeclarationBody::Record {
            declaration: decl, ..
        } = &d.body
        {
            let mut register =
                |elaborator: &mut Elaborator| -> Result<deppy_core::DefId, deppy_elab::Error> {
                    let record = elaborator.declare_record(record_id, decl.clone())?;
                    let id = elaborator.define(&d.name, Some(&d.ty), &record.ty())?;
                    let constructor_id = elaborator.define(
                        lower::constructor_name(&d.name),
                        None,
                        &record.constructor(),
                    )?;
                    constructors.push((d.name.clone(), constructor_id, d.span));
                    Ok(id)
                };
            let id = register(&mut elaborator).map_err(elab_diagnostic)?;
            record_id += 1;
            if module.public_names.contains(&d.name) {
                definitions.push((d.name, id, d.span));
            }
            continue;
        }
        let body = match &d.body {
            DeclarationBody::Structural(function) => match elaborator.lower_function(function) {
                Ok(body) => body,
                Err(error) => {
                    diagnostics.push(elab_diagnostic(error));
                    continue;
                }
            },
            DeclarationBody::Expression(body) => body.clone(),
            DeclarationBody::Record { .. } | DeclarationBody::Axiom | DeclarationBody::Data(_) => {
                unreachable!()
            }
        };
        let result = if d.opaque {
            elaborator.define_opaque(&d.name, Some(&d.ty), &body)
        } else {
            elaborator.define(&d.name, Some(&d.ty), &body)
        };
        let id = match result {
            Ok(id) => id,
            Err(error) => {
                diagnostics.push(elab_diagnostic(error));
                continue;
            }
        };
        if module.public_names.contains(&d.name) {
            definitions.push((d.name, id, d.span));
        }
    }
    let mut axiom_dependencies = std::collections::BTreeMap::new();
    for (name, id, span) in &definitions {
        let ids = elaborator
            .kernel()
            .axiom_dependencies(&deppy_core::Term::Global(*id).arc())
            .map_err(|e| Diagnostic {
                details: Default::default(),
                span: *span,
                message: e.to_string(),
            })?;
        axiom_dependencies.insert(
            name.clone(),
            ids.into_iter().map(|id| axiom_names[&id].clone()).collect(),
        );
    }
    let interface = CheckedInterface::from_checked(
        &elaborator,
        &definitions,
        &constructors,
        &axiom_dependencies,
        &data_entries,
    );
    Ok(CheckedModule {
        interface,
        axiom_dependencies,
        elaborator,
        definitions,
        constructors,
    })
}
