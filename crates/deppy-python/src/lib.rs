//! Static Python frontend using pinned Ruff components. No user code is executed.
mod lower;
mod modules;
use deppy_elab::{Elaborator, Expr};
pub use modules::{lower_module_with_resolver, FileResolver, SourceResolver};
use ruff_python_ast::PythonVersion;
use ruff_text_size::TextRange;

/// UTF-8 byte offsets in the original source, with an exclusive end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}
impl From<TextRange> for Span {
    fn from(range: TextRange) -> Self {
        Self {
            start: range.start().to_usize(),
            end: range.end().to_usize(),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
}
impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}..{}: {}",
            self.span.start, self.span.end, self.message
        )
    }
}
impl std::error::Error for Diagnostic {}
#[derive(Clone, Copy, Debug)]
pub enum Target {
    Python312,
    Python313,
    Python314,
}
impl Target {
    fn version(self) -> PythonVersion {
        match self {
            Self::Python312 => PythonVersion::PY312,
            Self::Python313 => PythonVersion::PY313,
            Self::Python314 => PythonVersion::PY314,
        }
    }
}
#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: String,
    pub span: Span,
    pub ty: Expr,
    pub body: DeclarationBody,
}
#[derive(Clone, Debug)]
pub enum DeclarationBody {
    Axiom,
    Expression(Expr),
    Structural(deppy_elab::lower::Function),
    Record {
        declaration: deppy_elab::RecordDecl,
        field_names: Vec<String>,
    },
}
#[derive(Clone, Debug)]
pub struct Module {
    pub declarations: Vec<Declaration>,
    pub public_names: std::collections::HashSet<String>,
    pub origins: std::collections::HashMap<String, String>,
}
pub struct CheckedModule {
    pub elaborator: Elaborator,
    pub axiom_dependencies: std::collections::BTreeMap<String, Vec<String>>,
    pub definitions: Vec<(String, deppy_core::DefId, Span)>,
    pub constructors: Vec<(String, deppy_core::DefId, Span)>,
}

/// Parse Python, reject target-version syntax errors, and lower the supported subset.
/// Ordinary undecorated functions and module assertions are left unchecked.
/// This is not CPython compilation, erasure checking, or runtime code generation.
pub fn lower_module(source: &str, target: Target) -> Result<Module, Diagnostic> {
    lower_module_with_resolver(source, target, &mut |_: &str| Ok(None))
}

/// A fresh environment makes checking a module atomic from the caller's perspective.
pub fn check_module(source: &str, target: Target) -> Result<CheckedModule, Diagnostic> {
    check_lowered(lower_module(source, target)?)
}

pub fn check_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl SourceResolver,
) -> Result<CheckedModule, Diagnostic> {
    check_lowered(lower_module_with_resolver(source, target, resolver)?)
}

fn check_lowered(module: Module) -> Result<CheckedModule, Diagnostic> {
    // Dependent Fin motives and composed equality proofs (e.g. reverse_get)
    // exceed the small elaborator default. Keep checking explicitly bounded.
    let mut elaborator = Elaborator::new(1_000_000);
    let mut definitions = vec![];
    let mut record_id = 0;
    let mut constructors = vec![];
    let mut axiom_names = std::collections::HashMap::new();
    for d in module.declarations {
        let diagnostic = |message: String| {
            if let Some(origin) = module.origins.get(&d.name) {
                Diagnostic {
                    span: Span { start: 0, end: 0 },
                    message: format!(
                        "in {origin}, bytes {}..{}: {message}",
                        d.span.start, d.span.end
                    ),
                }
            } else {
                Diagnostic {
                    span: d.span,
                    message,
                }
            }
        };
        if matches!(d.body, DeclarationBody::Axiom) {
            let id = elaborator
                .declare_axiom(&d.name, &d.ty)
                .map_err(|e| diagnostic(e.to_string()))?;
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
            let id = register(&mut elaborator).map_err(|e| diagnostic(e.to_string()))?;
            record_id += 1;
            if module.public_names.contains(&d.name) {
                definitions.push((d.name, id, d.span));
            }
            continue;
        }
        let body = match &d.body {
            DeclarationBody::Structural(function) => elaborator
                .lower_function(function)
                .map_err(|e| diagnostic(e.to_string()))?,
            DeclarationBody::Expression(body) => body.clone(),
            DeclarationBody::Record { .. } | DeclarationBody::Axiom => unreachable!(),
        };
        let id = elaborator
            .define(&d.name, Some(&d.ty), &body)
            .map_err(|e| diagnostic(e.to_string()))?;
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
                span: *span,
                message: e.to_string(),
            })?;
        axiom_dependencies.insert(
            name.clone(),
            ids.into_iter().map(|id| axiom_names[&id].clone()).collect(),
        );
    }
    Ok(CheckedModule {
        axiom_dependencies,
        elaborator,
        definitions,
        constructors,
    })
}
