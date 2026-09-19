//! Kernel-check lowered declarations before exposing a module interface.
use crate::*;

#[derive(Clone)]
pub(crate) struct LinkSnapshot {
    elaborator: Elaborator,
    record_id: u64,
    data_id: u64,
    data_entries: std::collections::BTreeMap<String, (u64, Option<usize>)>,
    constructors: Vec<(String, deppy_core::DefId, Span)>,
    axiom_names: std::collections::HashMap<deppy_core::DefId, String>,
    processed: std::collections::HashSet<String>,
    projections:
        std::collections::BTreeMap<String, std::collections::BTreeMap<String, deppy_core::Tm>>,
}
impl LinkSnapshot {
    fn new(options: FrontendOptions) -> Self {
        Self {
            elaborator: Elaborator::new(options.elaboration_steps),
            record_id: 0,
            data_id: 0,
            data_entries: Default::default(),
            constructors: vec![],
            axiom_names: Default::default(),
            processed: Default::default(),
            projections: Default::default(),
        }
    }
}
pub(crate) fn check_lowered(
    module: Module,
    options: FrontendOptions,
    diagnostics: &mut Vec<Diagnostic>,
) -> Result<CheckedModule, Diagnostic> {
    check_lowered_cached(module, options, diagnostics, None).map(|(checked, _, _)| checked)
}
pub(crate) fn check_lowered_cached(
    module: Module,
    options: FrontendOptions,
    diagnostics: &mut Vec<Diagnostic>,
    cached: Option<LinkSnapshot>,
) -> Result<(CheckedModule, LinkSnapshot, usize), Diagnostic> {
    let mut state = cached.unwrap_or_else(|| LinkSnapshot::new(options));
    let mut dependency_snapshot = None;
    let mut reused = 0;
    let mut definitions = vec![];
    let LinkSnapshot {
        elaborator,
        record_id,
        data_id,
        data_entries,
        constructors,
        axiom_names,
        processed,
        projections,
    } = &mut state;
    for d in module.declarations {
        if !module.origins.contains_key(&d.name) && dependency_snapshot.is_none() {
            dependency_snapshot = Some(LinkSnapshot {
                elaborator: elaborator.clone(),
                record_id: *record_id,
                data_id: *data_id,
                data_entries: data_entries.clone(),
                constructors: constructors.clone(),
                axiom_names: axiom_names.clone(),
                processed: processed.clone(),
                projections: projections.clone(),
            });
        }
        if processed.contains(&d.name) {
            reused += 1;
            continue;
        }
        processed.insert(d.name.clone());
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
                .declare_data(*data_id, decl.clone())
                .map_err(elab_diagnostic)?;
            for (index, (name, _)) in exports.iter().enumerate() {
                data_entries.insert(name.clone(), (*data_id, index.checked_sub(1)));
            }
            *data_id += 1;
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
            declaration: decl,
            field_names,
        } = &d.body
        {
            let mut register =
                |elaborator: &mut Elaborator| -> Result<deppy_core::DefId, deppy_elab::Error> {
                    let record = elaborator.declare_record(*record_id, decl.clone())?;
                    let id = elaborator.define(&d.name, Some(&d.ty), &record.ty())?;
                    let constructor_id = elaborator.define(
                        lower::constructor_name(&d.name),
                        None,
                        &record.constructor(),
                    )?;
                    constructors.push((d.name.clone(), constructor_id, d.span));
                    let fields = field_names
                        .iter()
                        .zip(&decl.fields)
                        .map(|(name, (binding, _))| {
                            let projection = record.projection(binding)?;
                            Ok((name.clone(), elaborator.infer(&projection)?.term))
                        })
                        .collect::<Result<_, deppy_elab::Error>>()?;
                    projections.insert(d.name.clone(), fields);
                    Ok(id)
                };
            let id = register(elaborator).map_err(elab_diagnostic)?;
            *record_id += 1;
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
    let mut exported = vec![];
    let mut exported_data = std::collections::BTreeMap::new();
    let mut exported_constructors = vec![];
    let mut exported_dependencies = std::collections::BTreeMap::new();
    for (alias, canonical) in &module.public_bindings {
        let Some(id) = elaborator.definition_id(canonical) else {
            continue;
        };
        let span = definitions
            .iter()
            .find(|(_, other, _)| *other == id)
            .map_or(Span { start: 0, end: 0 }, |(_, _, span)| *span);
        exported.push((alias.clone(), id, span));
        if let Some(metadata) = data_entries.get(canonical) {
            exported_data.insert(alias.clone(), *metadata);
        }
        if let Some((_, id, span)) = constructors.iter().find(|(name, _, _)| name == canonical) {
            exported_constructors.push((alias.clone(), *id, *span));
        }
        let dependencies = elaborator
            .kernel()
            .axiom_dependencies(&deppy_core::Term::Global(id).arc())
            .map_err(|e| Diagnostic {
                details: Default::default(),
                span,
                message: e.to_string(),
            })?;
        exported_dependencies.insert(
            alias.clone(),
            dependencies
                .into_iter()
                .map(|id| axiom_names[&id].clone())
                .collect(),
        );
    }
    let mut interface = CheckedInterface::from_checked(
        elaborator,
        &exported,
        &exported_constructors,
        &exported_dependencies,
        &exported_data,
    );
    for (alias, canonical) in &module.public_bindings {
        if let Some(fields) = projections.get(canonical) {
            interface.set_projections(alias, fields.clone());
        }
    }
    let dependency_snapshot = dependency_snapshot.unwrap_or_else(|| state.clone());
    Ok((
        CheckedModule {
            interface,
            axiom_dependencies,
            elaborator: state.elaborator,
            definitions,
            constructors: state.constructors,
        },
        dependency_snapshot,
        reused,
    ))
}
