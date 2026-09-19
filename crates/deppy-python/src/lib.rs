//! Static Python frontend using pinned Ruff components. No user code is executed.
mod interface;
mod linker;
mod lower;
use linker::check_lowered;
mod modules;
mod report;
use deppy_elab::{Elaborator, Expr};
pub use interface::{CheckedInterface, DeclarationKind, InductiveMetadata, InterfaceEntry};
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
    pub details: Box<DiagnosticDetails>,
    pub span: Span,
    pub message: String,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DiagnosticDetails {
    pub goals: Vec<deppy_elab::Goal>,
    pub source: Option<String>,
    pub line: Option<usize>,
    pub column: Option<usize>,
    pub kind: DiagnosticKind,
    pub related: Vec<deppy_elab::SourceLocation>,
    pub expected: Option<String>,
    pub actual: Option<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum DiagnosticKind {
    #[default]
    Frontend,
    Elaboration,
    Kernel,
}

impl Diagnostic {
    pub(crate) fn in_source(mut self, name: &str, source: &str) -> Self {
        self.details.source = Some(name.into());
        if let Some(prefix) = source.get(..self.span.start) {
            self.details.line = Some(prefix.bytes().filter(|b| *b == b'\n').count() + 1);
            self.details.column =
                Some(prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1);
        }
        self
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (&self.details.source, self.details.line, self.details.column) {
            (Some(source), Some(line), Some(column)) if !source.is_empty() => {
                write!(f, "{source}:{line}:{column}: {}", self.message)
            }
            _ => write!(
                f,
                "{}..{}: {}",
                self.span.start, self.span.end, self.message
            ),
        }
    }
}
impl std::error::Error for Diagnostic {}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Python312,
    Python313,
    Python314,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrontendOptions {
    pub target: Target,
    pub elaboration_steps: usize,
    pub lowering_steps: usize,
}
impl Default for FrontendOptions {
    fn default() -> Self {
        Self {
            target: Target::Python314,
            elaboration_steps: 1_000_000,
            lowering_steps: 20_000,
        }
    }
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
    pub opaque: bool,
    pub name: String,
    pub span: Span,
    pub ty: Expr,
    pub body: DeclarationBody,
}
#[derive(Clone, Debug)]
pub enum DeclarationBody {
    Data(deppy_elab::NamedDataDecl),
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
    pub source_names: std::collections::HashMap<String, String>,
    pub sources: std::collections::HashMap<String, String>,
    pub declarations: Vec<Declaration>,
    pub public_names: std::collections::HashSet<String>,
    /// Public source aliases mapped to canonical checked names.
    pub public_bindings: std::collections::BTreeMap<String, String>,
    pub origins: std::collections::HashMap<String, String>,
}
pub struct CheckedModule {
    pub interface: CheckedInterface,
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
    check_module_with_options(
        source,
        FrontendOptions {
            target,
            ..Default::default()
        },
    )
}

pub fn check_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl SourceResolver,
) -> Result<CheckedModule, Diagnostic> {
    check_module_with_options_and_resolver(
        source,
        FrontendOptions {
            target,
            ..Default::default()
        },
        resolver,
    )
}

pub fn check_module_with_options(
    source: &str,
    options: FrontendOptions,
) -> Result<CheckedModule, Diagnostic> {
    check_module_with_options_and_resolver(source, options, &mut |_: &str| Ok(None))
}

pub fn check_module_with_options_and_resolver(
    source: &str,
    options: FrontendOptions,
    resolver: &mut impl SourceResolver,
) -> Result<CheckedModule, Diagnostic> {
    let mut diagnostics = Vec::new();
    let checked = check_lowered(
        modules::lower_with_options(source, options, resolver)?,
        options,
        &mut diagnostics,
    )?;
    if diagnostics.is_empty() {
        Ok(checked)
    } else {
        Err(diagnostics.remove(0))
    }
}

/// Analysis never turns unfinished goals into checked declarations.
pub struct Analysis {
    pub checked: Option<CheckedModule>,
    pub diagnostics: Vec<Diagnostic>,
    pub goals: Vec<deppy_elab::Goal>,
}

impl Analysis {
    /// Assign a display identity to the root source, preserving imported identities.
    pub fn set_root_source_name(&mut self, name: &str) {
        fn set_location(location: &mut deppy_elab::SourceLocation, name: &str) {
            if location.source.is_empty() {
                location.source = name.to_owned();
            }
        }
        for diagnostic in &mut self.diagnostics {
            if diagnostic
                .details
                .source
                .as_deref()
                .is_none_or(str::is_empty)
            {
                diagnostic.details.source = Some(name.to_owned());
            }
            for location in &mut diagnostic.details.related {
                set_location(location, name);
            }
            for goal in &mut diagnostic.details.goals {
                if let Some(location) = &mut goal.location {
                    set_location(location, name);
                }
            }
        }
        for goal in &mut self.goals {
            if let Some(location) = &mut goal.location {
                set_location(location, name);
            }
        }
    }
}

pub fn analyze_module(source: &str, target: Target) -> Analysis {
    analyze_module_with_resolver(source, target, &mut |_: &str| Ok(None))
}

pub fn analyze_module_with_options(source: &str, options: FrontendOptions) -> Analysis {
    analyze_module_with_options_and_resolver(source, options, &mut |_: &str| Ok(None))
}

pub fn analyze_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl SourceResolver,
) -> Analysis {
    analyze_module_with_options_and_resolver(
        source,
        FrontendOptions {
            target,
            ..Default::default()
        },
        resolver,
    )
}

pub fn analyze_module_with_options_and_resolver(
    source: &str,
    options: FrontendOptions,
    resolver: &mut impl SourceResolver,
) -> Analysis {
    let mut diagnostics = Vec::new();
    let result = modules::lower_with_options(source, options, resolver)
        .and_then(|module| check_lowered(module, options, &mut diagnostics));
    let checked = match result {
        Ok(checked) if diagnostics.is_empty() => Some(checked),
        Ok(_) => None,
        Err(error) => {
            diagnostics.push(error);
            None
        }
    };
    let mut goals = Vec::new();
    for diagnostic in &mut diagnostics {
        for goal in &mut diagnostic.details.goals {
            goal.id = goals.len();
            goals.push(goal.clone());
        }
    }
    Analysis {
        checked,
        diagnostics,
        goals,
    }
}

/// Reuse immutable checked dependency snapshots across root modules. A change
/// to any dependency source or checking option invalidates the snapshot; failed
/// checks never publish partial environments into the cache.
#[derive(Default)]
pub struct CheckSession {
    snapshot: Option<linker::LinkSnapshot>,
    sources: std::collections::HashMap<String, String>,
    options: Option<FrontendOptions>,
    reused_declarations: usize,
}
impl CheckSession {
    pub fn reused_declarations(&self) -> usize {
        self.reused_declarations
    }
    pub fn check(
        &mut self,
        source: &str,
        options: FrontendOptions,
        resolver: &mut impl SourceResolver,
    ) -> Result<CheckedModule, Diagnostic> {
        self.reused_declarations = 0;
        let module = modules::lower_with_options(source, options, resolver)?;
        let sources = module
            .sources
            .iter()
            .filter(|(name, _)| !name.is_empty())
            .map(|(name, source)| (name.clone(), source.clone()))
            .collect::<std::collections::HashMap<_, _>>();
        let cached = if self.options == Some(options) && self.sources == sources {
            self.snapshot.clone()
        } else {
            None
        };
        let mut diagnostics = vec![];
        let (checked, snapshot, reused) =
            linker::check_lowered_cached(module, options, &mut diagnostics, cached)?;
        if !diagnostics.is_empty() {
            return Err(diagnostics.remove(0));
        }
        self.snapshot = Some(snapshot);
        self.sources = sources;
        self.options = Some(options);
        self.reused_declarations = reused;
        Ok(checked)
    }
}
