//! Static source linking. No Python import machinery or user code is executed.
mod registry;
mod resolver;
use crate::{Declaration, DeclarationBody, Diagnostic, Module, Span, Target};
use registry::{builtin_exports, declares_builtins, is_builtin, standard};
pub use resolver::{FileResolver, SourceResolver};
use ruff_python_ast::{Mod, Stmt};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub(crate) struct DataBinding {
    pub family: String,
    pub constructors: Vec<(String, usize)>,
    pub parameters: usize,
    pub indices: usize,
    pub constructor: Option<usize>,
}
#[derive(Clone, Debug)]
pub(crate) struct Binding {
    pub name: String,
    pub builtin: Option<String>,
    pub record: Option<(usize, usize)>,
    pub nullary: bool,
    pub verified: bool,
    pub contract: Option<crate::lower::Contract>,
    pub data: Option<DataBinding>,
}
type Exports = HashMap<String, Binding>;

impl Binding {
    fn builtin(name: &str) -> Self {
        Self {
            name: name.into(),
            builtin: Some(name.into()),
            record: None,
            verified: false,
            contract: None,
            nullary: false,
            data: None,
        }
    }
}

fn error(message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        details: Default::default(),
        span: Span { start: 0, end: 0 },
        message: message.into(),
    }
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
        details: Default::default(),
        span: e.location.into(),
        message: e.to_string(),
    })?;
    if let Some(e) = parsed.unsupported_syntax_errors().first() {
        return Err(Diagnostic {
            details: Default::default(),
            span: e.range.into(),
            message: format!("unsupported target-version syntax: {:?}", e.kind),
        });
    }
    let Mod::Module(module) = parsed.into_syntax() else {
        unreachable!()
    };
    Ok(module.body.into_iter().collect())
}

// Compiler forms are declared in bundled sources, but have no checked Python
// body to lower. User modules cannot introduce @builtin declarations.
fn extract_builtin_declarations(
    name: &str,
    body: Vec<Stmt>,
) -> Result<(Vec<Stmt>, Exports), Diagnostic> {
    if !declares_builtins(name) {
        return Ok((body, Exports::new()));
    }
    let mut remaining = Vec::new();
    let mut exports = Exports::new();
    for stmt in body {
        let declaration = match &stmt {
            Stmt::FunctionDef(f) => Some((f.name.as_str(), &f.decorator_list, &f.body)),
            Stmt::ClassDef(c) => Some((c.name.as_str(), &c.decorator_list, &c.body)),
            _ => None,
        };
        if let Some((builtin, decorators, statements)) = declaration {
            let marked = decorators.len() == 1
                && matches!(&decorators[0].expression, ruff_python_ast::Expr::Name(n) if n.id.as_str() == "builtin");
            if marked {
                if !is_builtin(builtin)
                    || statements.len() != 1
                    || !matches!(&statements[0], Stmt::Expr(e) if matches!(e.value.as_ref(), ruff_python_ast::Expr::EllipsisLiteral(_)))
                    || exports
                        .insert(builtin.into(), Binding::builtin(builtin))
                        .is_some()
                {
                    return Err(error(format!(
                        "invalid compiler builtin declaration: {name}.{builtin}"
                    )));
                }
                continue;
            }
        }
        remaining.push(stmt);
    }
    Ok((remaining, exports))
}

pub fn lower_module_with_resolver(
    source: &str,
    target: Target,
    resolver: &mut impl SourceResolver,
) -> Result<Module, Diagnostic> {
    lower_with_options(
        source,
        crate::FrontendOptions {
            target,
            ..Default::default()
        },
        resolver,
    )
}

pub(crate) fn lower_with_options(
    source: &str,
    options: crate::FrontendOptions,
    resolver: &mut impl SourceResolver,
) -> Result<Module, Diagnostic> {
    let mut loader = Loader {
        resolver,
        sources: HashMap::new(),
        source_names: HashMap::new(),
        target: options.target,
        lowering_steps: options.lowering_steps,
        loaded: HashMap::new(),
        active: HashSet::new(),
        declarations: vec![],
        origins: HashMap::new(),
        total_bytes: 0,
    };
    let root = loader.lower("", source).map_err(|e| {
        if e.details.source.is_some() {
            e
        } else {
            e.in_source("", source)
        }
    })?;
    Ok(Module {
        sources: loader.sources,
        source_names: loader.source_names,
        declarations: loader.declarations,
        public_bindings: root
            .iter()
            .filter(|(_, b)| b.builtin.is_none())
            .map(|(name, b)| (name.clone(), b.name.clone()))
            .collect(),
        public_names: root
            .values()
            .filter(|b| !b.name.contains('.'))
            .map(|b| b.name.clone())
            .collect(),
        origins: loader.origins,
    })
}
struct Loader<'a, R> {
    sources: HashMap<String, String>,
    source_names: HashMap<String, String>,
    resolver: &'a mut R,
    target: Target,
    lowering_steps: usize,
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
        let source_name = self.resolver.source_name(name);
        self.source_names.insert(name.into(), source_name.clone());
        let exports = self.lower(name, &source).map_err(|e| {
            if e.details.source.is_some() {
                e
            } else {
                e.in_source(&source_name, &source)
            }
        })?;
        self.active.remove(name);
        self.loaded.insert(name.into(), exports.clone());
        Ok(exports)
    }
    fn lower(&mut self, name: &str, source: &str) -> Result<Exports, Diagnostic> {
        self.sources.insert(name.into(), source.into());
        self.total_bytes += source.len();
        if self.total_bytes > 8_000_000 {
            return Err(error("checked module graph exceeds source size limit"));
        }
        let (body, declared_builtins) =
            extract_builtin_declarations(name, parse(source, self.target)?)?;
        let mut libraries = HashMap::new();
        let mut exports = builtin_exports(name);
        exports.extend(declared_builtins);
        for stmt in &body {
            if let Stmt::ImportFrom(import) = stmt {
                if import.level != 0 || import.is_lazy {
                    return Err(error("only absolute eager source imports are supported"));
                }
                let module = import.module.as_ref().map_or("", |m| m.as_str());
                let available = self.load(module)?;
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
        // Link only the checked interpreters/operators used by verified bodies.
        // Public imports are still resolved above; synthetic names cannot be
        // supplied by source programs.
        #[derive(Default)]
        struct VerifiedLibraries {
            loops: bool,
            arithmetic: bool,
            integer: bool,
        }
        impl<'a> ruff_python_ast::visitor::Visitor<'a> for VerifiedLibraries {
            fn visit_stmt(&mut self, statement: &'a Stmt) {
                self.loops |= matches!(statement, Stmt::For(_));
                ruff_python_ast::visitor::walk_stmt(self, statement);
            }
            fn visit_operator(&mut self, op: &'a ruff_python_ast::Operator) {
                self.arithmetic |= matches!(
                    op,
                    ruff_python_ast::Operator::Sub
                        | ruff_python_ast::Operator::FloorDiv
                        | ruff_python_ast::Operator::Mod
                );
            }
            fn visit_unary_op(&mut self, op: &'a ruff_python_ast::UnaryOp) {
                self.integer |= *op == ruff_python_ast::UnaryOp::USub;
            }
        }
        let mut needed = VerifiedLibraries::default();
        for statement in &body {
            if let Stmt::FunctionDef(f) = statement {
                if f.decorator_list.iter().any(|d| {
                    let decorator = match &d.expression { ruff_python_ast::Expr::Call(c) => c.func.as_ref(), e => e };
                    matches!(decorator, ruff_python_ast::Expr::Name(n) if exports.get(n.id.as_str()).is_some_and(|b| b.builtin.as_deref() == Some("verified")))
                }) {
                    for statement in &f.body {
                        ruff_python_ast::visitor::Visitor::visit_stmt(&mut needed, statement);
                    }
                }
            }
        }
        if needed.loops {
            self.load("deppy.verified_loop")?;
        }
        if needed.arithmetic {
            self.load("deppy.arithmetic")?;
        }
        if needed.integer {
            self.load("deppy.integer")?;
        }
        let declarations = crate::lower::module(&body, name, &libraries, self.lowering_steps)?;
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
                    builtin: None,
                    record,
                    nullary,
                    verified: matches!(d.body, DeclarationBody::Verified { .. }),
                    contract: crate::lower::Contract::from_declaration(d),
                    data: match &d.body {
                        DeclarationBody::Data(decl) => Some(DataBinding {
                            family: decl.name.clone(),
                            constructors: decl
                                .constructors
                                .iter()
                                .map(|c| (c.name.clone(), c.fields.len()))
                                .collect(),
                            parameters: decl.parameters.len(),
                            indices: decl.indices.len(),
                            constructor: None,
                        }),
                        _ => None,
                    },
                },
            );
            if !name.is_empty() {
                self.origins.insert(d.name.clone(), name.into());
            }
        }
        for d in &declarations {
            if let DeclarationBody::Data(decl) = &d.body {
                for (c, ctor) in decl.constructors.iter().enumerate() {
                    let local = ctor.name.rsplit('.').next().unwrap();
                    exports.insert(
                        local.into(),
                        Binding {
                            name: ctor.name.clone(),
                            builtin: None,
                            record: None,
                            verified: false,
                            contract: None,
                            nullary: ctor.fields.is_empty(),
                            data: Some(DataBinding {
                                family: decl.name.clone(),
                                constructors: decl
                                    .constructors
                                    .iter()
                                    .map(|c| (c.name.clone(), c.fields.len()))
                                    .collect(),
                                parameters: decl.parameters.len(),
                                indices: 0,
                                constructor: Some(c),
                            }),
                        },
                    );
                    if !name.is_empty() {
                        self.origins.insert(ctor.name.clone(), name.into());
                    }
                }
            }
        }
        self.declarations.extend(declarations);
        Ok(exports)
    }
}

#[cfg(test)]
mod builtin_declaration_tests {
    use super::{extract_builtin_declarations, parse, Target};

    #[test]
    fn bundled_builtin_declarations_are_validated_and_exported() {
        let target = Target::Python314;
        for (module, source, example) in [
            (
                "deppy._builtins",
                include_str!("../stdlib/deppy/_builtins.py"),
                "Nat",
            ),
            (
                "deppy.tactics",
                include_str!("../stdlib/deppy/tactics.py"),
                "rewrite",
            ),
        ] {
            let (_, exports) =
                extract_builtin_declarations(module, parse(source, target).unwrap()).unwrap();
            assert_eq!(exports[example].builtin.as_deref(), Some(example));
        }
        let malformed = "@builtin\ndef exact(proof):\n    return proof\n";
        assert!(
            extract_builtin_declarations("deppy.tactics", parse(malformed, target).unwrap())
                .is_err()
        );
        let (_, user_exports) = extract_builtin_declarations(
            "client",
            parse("@builtin\ndef exact(proof): ...\n", target).unwrap(),
        )
        .unwrap();
        assert!(user_exports.is_empty());
    }
}
