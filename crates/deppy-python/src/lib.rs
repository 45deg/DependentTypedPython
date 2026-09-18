//! Static Python frontend using pinned Ruff components. No user code is executed.
mod lower;
use deppy_elab::{Elaborator, Expr};
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
    Expression(Expr),
    Structural(deppy_elab::lower::Function),
}
#[derive(Clone, Debug)]
pub struct Module {
    pub declarations: Vec<Declaration>,
}
pub struct CheckedModule {
    pub elaborator: Elaborator,
    pub definitions: Vec<(String, deppy_core::DefId, Span)>,
}

/// Parse Python, reject target-version syntax errors, and lower the supported subset.
/// Ordinary undecorated functions and module assertions are left unchecked.
/// This is not CPython compilation, erasure checking, or runtime code generation.
pub fn lower_module(source: &str, target: Target) -> Result<Module, Diagnostic> {
    use ruff_python_parser::{Mode, ParseOptions};
    if source.len() > 1_000_000 {
        return Err(Diagnostic {
            span: Span { start: 0, end: 0 },
            message: "source exceeds frontend size limit".into(),
        });
    }
    let parsed = ruff_python_parser::parse(
        source,
        ParseOptions::from(Mode::Module).with_target_version(target.version()),
    )
    .map_err(|e| Diagnostic {
        span: e.location.into(),
        message: e.to_string(),
    })?;
    if let Some(e) = parsed.unsupported_syntax_errors().first() {
        return Err(Diagnostic {
            span: e.range.into(),
            message: format!("unsupported target-version syntax: {:?}", e.kind),
        });
    }
    let ruff_python_ast::Mod::Module(module) = parsed.syntax() else {
        unreachable!()
    };
    lower::module(&module.body)
}

/// A fresh environment makes checking a module atomic from the caller's perspective.
pub fn check_module(source: &str, target: Target) -> Result<CheckedModule, Diagnostic> {
    let module = lower_module(source, target)?;
    let mut elaborator = Elaborator::default();
    let mut definitions = vec![];
    for d in module.declarations {
        let body =
            match &d.body {
                DeclarationBody::Structural(function) => elaborator
                    .lower_function(function)
                    .map_err(|e| Diagnostic {
                        span: d.span,
                        message: e.to_string(),
                    })?,
                DeclarationBody::Expression(body) => body.clone(),
            };
        let id = elaborator
            .define(&d.name, Some(&d.ty), &body)
            .map_err(|e| Diagnostic {
                span: d.span,
                message: e.to_string(),
            })?;
        definitions.push((d.name, id, d.span));
    }
    Ok(CheckedModule {
        elaborator,
        definitions,
    })
}
