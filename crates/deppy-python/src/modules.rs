//! Static source linking. No Python import machinery or user code is executed.
use crate::{Declaration, DeclarationBody, Diagnostic, Module, Span, Target};
use ruff_python_ast::{Mod, Stmt};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub name: String,
    pub record: Option<(usize, usize)>,
    pub nullary: bool,
}
type Exports = HashMap<String, Binding>;

/// Return source for a checked module name. None means the module is unavailable.
/// The resolver supplies data, never executed Python objects.
pub trait SourceResolver {
    fn source(&mut self, name: &str) -> Result<Option<String>, String>;
}
impl<F: FnMut(&str) -> Result<Option<String>, String>> SourceResolver for F {
    fn source(&mut self, name: &str) -> Result<Option<String>, String> {
        self(name)
    }
}
fn error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        span: Span { start: 0, end: 0 },
        message: message.into(),
    }
}
fn standard(name: &str) -> Option<&'static str> {
    match name {
        "deppy.vectors" => Some(include_str!("../stdlib/deppy/vectors.py")),
        "deppy.fin" => Some(include_str!("../stdlib/deppy/fin.py")),
        "deppy.equality" => Some(include_str!("../stdlib/deppy/equality.py")),
        _ => None,
    }
}
fn facade(name: &str) -> bool {
    matches!(name, "cong" | "trans" | "sym" | "transport")
}
fn parse(source: &str, target: Target) -> Result<Vec<Stmt>, Diagnostic> {
    use ruff_python_parser::{Mode, ParseOptions};
    if source.len() > 1_000_000 {
        return Err(error("source exceeds frontend size limit"));
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
    let Mod::Module(module) = parsed.into_syntax() else {
        unreachable!()
    };
    Ok(module.body.into_iter().collect())
}

pub fn lower_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl SourceResolver,
) -> Result<Module, Diagnostic> {
    let mut loader = Loader {
        resolver,
        target,
        loaded: HashMap::new(),
        active: HashSet::new(),
        declarations: vec![],
        origins: HashMap::new(),
        total_bytes: 0,
    };
    let root = loader.lower("", source)?;
    Ok(Module {
        declarations: loader.declarations,
        public_names: root
            .values()
            .filter(|b| !b.name.contains('.'))
            .map(|b| b.name.clone())
            .collect(),
        origins: loader.origins,
    })
}
struct Loader<'a, R> {
    resolver: &'a mut R,
    target: Target,
    loaded: HashMap<String, Exports>,
    active: HashSet<String>,
    declarations: Vec<Declaration>,
    origins: HashMap<String, String>,
    total_bytes: usize,
}
impl<R: SourceResolver> Loader<'_, R> {
    fn load(&mut self, name: &str) -> Result<Exports, Diagnostic> {
        if let Some(exports) = self.loaded.get(name) {
            return Ok(exports.clone());
        }
        if !self.active.insert(name.into()) {
            return Err(error(format!("cyclic checked import: {name}")));
        }
        if self.active.len() > 32 || self.loaded.len() > 128 {
            return Err(error("checked module graph exceeds limit"));
        }
        let source = if let Some(source) = standard(name) {
            source.into()
        } else {
            if name == "deppy" || name.starts_with("deppy.") {
                return Err(error(format!("unknown standard module: {name}")));
            }
            self.resolver
                .source(name)
                .map_err(error)?
                .ok_or_else(|| error(format!("checked module not found: {name}")))?
        };
        let exports = self.lower(name, &source).map_err(|e| {
            error(format!(
                "in {name}, bytes {}..{}: {}",
                e.span.start, e.span.end, e.message
            ))
        })?;
        self.active.remove(name);
        self.loaded.insert(name.into(), exports.clone());
        Ok(exports)
    }
    fn lower(&mut self, name: &str, source: &str) -> Result<Exports, Diagnostic> {
        self.total_bytes += source.len();
        if self.total_bytes > 8_000_000 {
            return Err(error("checked module graph exceeds source size limit"));
        }
        let body = parse(source, self.target)?;
        let mut libraries = HashMap::new();
        let mut exports = Exports::new();
        for stmt in &body {
            if let Stmt::ImportFrom(import) = stmt {
                if import.level != 0 || import.is_lazy {
                    return Err(error("only absolute eager source imports are supported"));
                }
                let module = import.module.as_ref().map_or("", |m| m.as_str());
                if module == "__future__" {
                    continue;
                }
                let available = if module == "deppy" {
                    if import.names.iter().any(|a| facade(a.name.as_str())) {
                        self.load("deppy.equality")?
                    } else {
                        Exports::new()
                    }
                } else {
                    self.load(module)?
                };
                for alias in &import.names {
                    if let Some(binding) = available.get(alias.name.as_str()) {
                        exports.insert(
                            alias.asname.as_ref().unwrap_or(&alias.name).to_string(),
                            binding.clone(),
                        );
                    }
                }
                libraries
                    .entry(module.to_owned())
                    .or_insert_with(Exports::new)
                    .extend(available);
            }
        }
        let declarations = crate::lower::module(&body, name, &libraries)?;
        for d in &declarations {
            let record = match &d.body {
                DeclarationBody::Record { declaration, .. } => {
                    Some((declaration.parameters.len(), declaration.fields.len()))
                }
                _ => None,
            };
            let local_name = if name.is_empty() {
                &d.name
            } else {
                d.name.strip_prefix(&format!("{name}.")).unwrap()
            };
            let nullary = body.iter().any(|s| matches!(s, Stmt::FunctionDef(f) if f.name.as_str() == local_name && f.parameters.posonlyargs.is_empty() && f.parameters.args.is_empty()));
            exports.insert(
                local_name.into(),
                Binding {
                    name: d.name.clone(),
                    record,
                    nullary,
                },
            );
            if !name.is_empty() {
                self.origins.insert(d.name.clone(), name.into());
            }
        }
        self.declarations.extend(declarations);
        Ok(exports)
    }
}

/// Resolve .py files (or package __init__.py files) under a fixed source root.
/// Canonical paths must stay inside that root, including through symlinks.
pub struct FileResolver {
    root: std::path::PathBuf,
}
impl FileResolver {
    pub fn new(root: impl AsRef<std::path::Path>) -> Result<Self, std::io::Error> {
        Ok(Self {
            root: root.as_ref().canonicalize()?,
        })
    }
}
impl SourceResolver for FileResolver {
    fn source(&mut self, name: &str) -> Result<Option<String>, String> {
        let mut relative = std::path::PathBuf::new();
        for part in name.split('.') {
            if part.is_empty() || !part.chars().all(|c| c == '_' || c.is_alphanumeric()) {
                return Err("invalid checked module name".into());
            }
            relative.push(part);
        }
        let file = self.root.join(&relative).with_extension("py");
        let package = self.root.join(relative).join("__init__.py");
        let candidate = if file.is_file() {
            file
        } else if package.is_file() {
            package
        } else {
            return Ok(None);
        };
        let path = candidate.canonicalize().map_err(|e| e.to_string())?;
        if !path.starts_with(&self.root) {
            return Err(format!("checked module escapes source root: {name}"));
        }
        if path.metadata().map_err(|e| e.to_string())?.len() > 1_000_000 {
            return Err(format!("source exceeds frontend size limit: {name}"));
        }
        std::fs::read_to_string(path)
            .map(Some)
            .map_err(|e| e.to_string())
    }
}
