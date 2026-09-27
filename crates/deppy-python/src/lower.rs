mod data;
mod expression;
mod matrix;
mod record;
mod structural;
mod verified;
use crate::{Declaration, DeclarationBody, Diagnostic};
use deppy_elab::{Expr as E, Plicity};
pub(crate) use record::constructor_name;
use ruff_python_ast::{self as ast, Expr, Stmt};
use ruff_text_size::{Ranged, TextRange};
use std::collections::{HashMap, HashSet};
pub(crate) use verified::{specification_name, Contract};
fn error(node: &impl Ranged, message: impl Into<String>) -> Diagnostic {
    Diagnostic {
        details: Default::default(),
        span: node.range().into(),
        message: message.into(),
    }
}
#[derive(Clone, Default)]
struct Scope {
    aliases: HashMap<String, String>,
    locals: HashSet<String>,
    assigned: HashSet<String>,
    fields: HashSet<String>,
    recursion: Option<(String, Vec<String>, usize)>,
}
struct Lowerer {
    imports: HashMap<String, String>,
    globals: HashMap<String, crate::modules::Binding>,
    namespace: String,
    remaining: usize,
    wildcard: usize,
    records: HashMap<String, (usize, usize)>,
}
pub(super) fn module(
    body: &[Stmt],
    namespace: &str,
    libraries: &HashMap<String, HashMap<String, crate::modules::Binding>>,
    lowering_steps: usize,
) -> Result<Vec<Declaration>, Diagnostic> {
    let mut l = Lowerer {
        imports: HashMap::new(),
        globals: HashMap::new(),
        namespace: namespace.into(),
        remaining: lowering_steps,
        wildcard: 0,
        records: HashMap::new(),
    };
    let mut declarations = vec![];
    let mut names = HashSet::new();
    let mut imports_done = false;
    for (i, stmt) in body.iter().enumerate() {
        match stmt {
            Stmt::Expr(e) if i == 0 && matches!(e.value.as_ref(), Expr::StringLiteral(_)) => {}
            Stmt::ImportFrom(import) => {
                if imports_done || import.level != 0 || import.is_lazy {
                    return Err(error(stmt, "only initial absolute imports are supported"));
                }
                let module = import.module.as_ref().map(|m| m.as_str()).unwrap_or("");
                if module == "deppy" || libraries.contains_key(module) {
                    for alias in &import.names {
                        let original = alias.name.as_str();
                        let name = alias.asname.as_ref().unwrap_or(&alias.name).as_str();
                        if !names.insert(name.to_owned()) {
                            return Err(error(alias, "duplicate module binding"));
                        }
                        if let Some(binding) = libraries
                            .get(module)
                            .and_then(|exports| exports.get(original))
                        {
                            if let Some(builtin) = &binding.builtin {
                                l.imports.insert(name.into(), builtin.clone());
                            } else {
                                l.globals.insert(name.into(), binding.clone());
                                if let Some(arity) = binding.record {
                                    l.records.insert(name.into(), arity);
                                }
                            }
                        } else {
                            return Err(error(
                                alias,
                                format!("unknown checked import: {module}.{original}"),
                            ));
                        }
                    }
                } else {
                    return Err(error(
                        stmt,
                        "only statically resolved imports are supported",
                    ));
                }
            }
            Stmt::FunctionDef(f) => {
                imports_done = true;
                if !names.insert(f.name.to_string()) {
                    return Err(error(f, "duplicate module binding"));
                }
                if f.decorator_list.is_empty() {
                    continue;
                }
                let decorator = match &f.decorator_list[0].expression {
                    Expr::Call(c) => c.func.as_ref(),
                    e => e,
                };
                let mut declaration = if l.builtin(decorator, &Scope::default()) == Some("verified")
                {
                    l.verified(f)?
                } else {
                    let is_axiom = f.decorator_list.len() == 1
                        && l.builtin(&f.decorator_list[0].expression, &Scope::default())
                            == Some("axiom");
                    let (decreases, opaque) = if is_axiom {
                        (None, false)
                    } else {
                        l.decorator(f)?
                    };
                    let mut declaration = l.function(f, decreases)?;
                    declaration.opaque = opaque;
                    declaration
                };
                declaration.name = l.qualified(f.name.as_str());
                l.globals.insert(
                    f.name.to_string(),
                    crate::modules::Binding {
                        name: declaration.name.clone(),
                        builtin: None,
                        record: None,
                        data: None,
                        verified: matches!(declaration.body, DeclarationBody::Verified { .. }),
                        contract: crate::lower::Contract::from_declaration(&declaration),
                        nullary: f.parameters.posonlyargs.is_empty()
                            && f.parameters.args.is_empty(),
                    },
                );
                declarations.push(declaration);
            }
            Stmt::ClassDef(class) => {
                imports_done = true;
                if !names.insert(class.name.to_string()) {
                    return Err(error(class, "duplicate module binding"));
                }
                let decorator = class.decorator_list.first().map(|d| match &d.expression {
                    Expr::Call(c) => c.func.as_ref(),
                    expr => expr,
                });
                if decorator.is_some_and(|d| l.builtin(d, &Scope::default()) == Some("inductive")) {
                    let declaration = l.data(class, &mut names)?;
                    declarations.push(declaration);
                    continue;
                }
                let mut declaration = l.record(class)?;
                declaration.name = l.qualified(class.name.as_str());
                l.globals.insert(
                    class.name.to_string(),
                    crate::modules::Binding {
                        name: declaration.name.clone(),
                        builtin: None,
                        record: l.records.get(class.name.as_str()).copied(),
                        data: None,
                        verified: false,
                        contract: None,
                        nullary: false,
                    },
                );
                declarations.push(declaration);
            }
            Stmt::If(statement) if is_main_guard(statement) => {
                // A script entry point is ordinary Python, never a checked export.
                imports_done = true;
            }
            Stmt::Assert(_) => {
                imports_done = true;
            }
            _ => return Err(error(stmt, "unsupported module statement")),
        }
    }
    Ok(declarations)
}
fn is_main_guard(statement: &ast::StmtIf) -> bool {
    if !statement.elif_else_clauses.is_empty() {
        return false;
    }
    let Expr::Compare(test) = statement.test.as_ref() else {
        return false;
    };
    test.ops.as_ref() == [ast::CmpOp::Eq]
        && matches!(test.left.as_ref(), Expr::Name(name) if name.id.as_str() == "__name__")
        && matches!(test.comparators.as_ref(), [Expr::StringLiteral(value)] if value.value.to_str() == "__main__")
}

impl Lowerer {
    fn qualified(&self, name: &str) -> String {
        if self.namespace.is_empty() {
            name.into()
        } else {
            format!("{}.{name}", self.namespace)
        }
    }
    fn tick(&mut self, range: TextRange) -> Result<(), Diagnostic> {
        self.remaining = self.remaining.checked_sub(1).ok_or_else(|| Diagnostic {
            details: Default::default(),
            span: range.into(),
            message: "frontend budget exhausted".into(),
        })?;
        Ok(())
    }
    fn builtin<'a>(&'a self, expr: &Expr, scope: &Scope) -> Option<&'a str> {
        let Expr::Name(name) = expr else {
            return None;
        };
        if scope.locals.contains(name.id.as_str()) || scope.assigned.contains(name.id.as_str()) {
            return None;
        }
        self.imports.get(name.id.as_str()).map(String::as_str)
    }
    fn bind(&self, scope: &mut Scope, name: &str, node: &impl Ranged) -> Result<(), Diagnostic> {
        if !scope.locals.insert(name.to_string()) {
            return Err(error(
                node,
                "duplicate binder or reassignment is not supported",
            ));
        }
        Ok(())
    }
    fn parameters(&self, parameters: &ast::Parameters) -> Result<(), Diagnostic> {
        if parameters.vararg.is_some()
            || parameters.kwarg.is_some()
            || !parameters.kwonlyargs.is_empty()
            || parameters
                .iter_non_variadic_params()
                .any(|p| p.default.is_some())
        {
            return Err(error(
                parameters,
                "variadic, keyword-only and default parameters are unsupported",
            ));
        }
        Ok(())
    }
    fn function(
        &mut self,
        f: &ast::StmtFunctionDef,
        decreases: Option<(String, u32)>,
    ) -> Result<Declaration, Diagnostic> {
        if f.is_async {
            return Err(error(f, "async dependent functions are unsupported"));
        }
        self.parameters(&f.parameters)?;
        let mut scope = Scope::default();
        let mut parameters = vec![];
        if let Some(params) = &f.type_params {
            for param in params.iter() {
                let ast::TypeParam::TypeVar(p) = param else {
                    return Err(error(param, "variadic type parameters are unsupported"));
                };
                if p.default.is_some() {
                    return Err(error(p, "default type parameters are unsupported"));
                }
                let bound = p
                    .bound
                    .as_deref()
                    .ok_or_else(|| error(p, "an explicit type parameter bound is required"))?;
                let ty = self.expr(bound, &scope)?;
                self.bind(&mut scope, p.name.as_str(), &p.name)?;
                parameters.push((p.name.to_string(), Plicity::Implicit, ty));
            }
        }
        for param in f.parameters.posonlyargs.iter().chain(&f.parameters.args) {
            let p = &param.parameter;
            let annotation = p
                .annotation
                .as_deref()
                .ok_or_else(|| error(p, "parameter annotation required"))?;
            let ty = self.expr(annotation, &scope)?;
            self.bind(&mut scope, p.name.as_str(), &p.name)?;
            parameters.push((p.name.to_string(), Plicity::Explicit, ty));
        }
        let mut ty = self.expr(
            f.returns
                .as_deref()
                .ok_or_else(|| error(f, "return annotation required"))?,
            &scope,
        )?;
        if f.decorator_list.len() == 1
            && self.builtin(&f.decorator_list[0].expression, &Scope::default()) == Some("axiom")
        {
            if f.body.len() != 1
                || !matches!(&f.body[0], Stmt::Expr(e) if matches!(e.value.as_ref(), Expr::EllipsisLiteral(_)))
            {
                return Err(error(f, "axiom body must be exactly ..."));
            }
            for (name, plicity, domain) in parameters.into_iter().rev() {
                ty = E::pi(name, plicity, domain, ty);
            }
            return Ok(Declaration {
                opaque: false,
                name: f.name.to_string(),
                span: f.range.into(),
                ty,
                body: DeclarationBody::Axiom,
            });
        }
        let decreases = decreases.or_else(|| {
            f.body.iter().find_map(|stmt| {
                if let Stmt::Match(m) = stmt {
                    if let Expr::Name(subject) = m.subject.as_ref() {
                        return Some((subject.id.to_string(), 0));
                    }
                }
                None
            })
        });
        if let Some((decreases, motive_level)) = decreases {
            let implicit = parameters
                .iter()
                .filter(|(_, p, _)| *p == Plicity::Implicit)
                .map(|(n, _, _)| n.clone())
                .collect();
            scope.recursion = Some((
                f.name.to_string(),
                implicit,
                f.parameters.posonlyargs.len() + f.parameters.args.len(),
            ));
            Self::capture_names(&f.body, &mut scope.assigned);
            let body = self.structural_body(&f.body, &scope)?;
            let function = deppy_elab::lower::Function {
                parameters: parameters
                    .iter()
                    .map(|(name, plicity, ty)| deppy_elab::lower::Parameter {
                        name: name.clone(),
                        plicity: *plicity,
                        ty: ty.clone(),
                    })
                    .collect(),
                result: ty.clone(),
                decreases,
                motive_level,
                body,
            };
            for (name, plicity, domain) in parameters.into_iter().rev() {
                ty = E::pi(name, plicity, domain, ty);
            }
            return Ok(Declaration {
                opaque: false,
                name: f.name.to_string(),
                span: f.range.into(),
                ty,
                body: DeclarationBody::Structural(function),
            });
        }
        // Python locals have function-wide scope. Hide globals/imports before an
        // assignment too, rather than interpreting a use-before-binding as a global.
        for stmt in &f.body {
            let target = match stmt {
                Stmt::Assign(s) if s.targets.len() == 1 => Some(&s.targets[0]),
                Stmt::AnnAssign(s) => Some(s.target.as_ref()),
                _ => None,
            };
            if let Some(Expr::Name(n)) = target {
                scope.assigned.insert(n.id.to_string());
            }
        }
        let mut lets = vec![];
        let mut result = None;
        for (i, stmt) in f.body.iter().enumerate() {
            self.tick(stmt.range())?;
            match stmt {
                Stmt::Expr(s) if i == 0 && matches!(s.value.as_ref(), Expr::StringLiteral(_)) => {}
                Stmt::Return(s) if i + 1 == f.body.len() => {
                    result = Some(
                        self.expr(
                            s.value
                                .as_deref()
                                .ok_or_else(|| error(s, "return value required"))?,
                            &scope,
                        )?,
                    );
                }
                Stmt::Assign(s) if s.targets.len() == 1 => {
                    let Expr::Name(name) = &s.targets[0] else {
                        return Err(error(s, "assignment requires a single local name"));
                    };
                    let value = self.expr(&s.value, &scope)?;
                    self.bind(&mut scope, name.id.as_str(), name)?;
                    lets.push((name.id.to_string(), None, value));
                }
                Stmt::AnnAssign(s) => {
                    let Expr::Name(name) = s.target.as_ref() else {
                        return Err(error(s, "assignment requires a single local name"));
                    };
                    let ty = self.expr(&s.annotation, &scope)?;
                    let value = self.expr(
                        s.value
                            .as_deref()
                            .ok_or_else(|| error(s, "local definition requires a value"))?,
                        &scope,
                    )?;
                    self.bind(&mut scope, name.id.as_str(), name)?;
                    lets.push((name.id.to_string(), Some(ty), value));
                }
                _ => {
                    return Err(error(
                        stmt,
                        "expected immutable local definitions followed by one return",
                    ))
                }
            }
        }
        let mut body = result.ok_or_else(|| error(f, "function must end with a return"))?;
        for (name, ty, value) in lets.into_iter().rev() {
            body = E::let_in(name, ty, value, body);
        }
        for (name, plicity, domain) in parameters.into_iter().rev() {
            ty = E::pi(&name, plicity, domain.clone(), ty);
            body = E::lam(name, plicity, Some(domain), body);
        }
        Ok(Declaration {
            opaque: false,
            name: f.name.to_string(),
            span: f.range.into(),
            ty,
            body: DeclarationBody::Expression(body),
        })
    }
}
