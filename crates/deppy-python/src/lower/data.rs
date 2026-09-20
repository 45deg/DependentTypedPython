use super::*;
use crate::modules::{Binding, DataBinding};

impl Lowerer {
    pub(super) fn data(
        &mut self,
        class: &ast::StmtClassDef,
        names: &mut HashSet<String>,
    ) -> Result<Declaration, Diagnostic> {
        if class.decorator_list.len() != 1
            || class
                .arguments
                .as_ref()
                .is_some_and(|a| !a.args.is_empty() || !a.keywords.is_empty())
        {
            return Err(error(
                class,
                "inductive declarations require one decorator and no bases",
            ));
        }
        let decorator = &class.decorator_list[0].expression;
        let level = if let Expr::Call(call) = decorator {
            if !call.arguments.args.is_empty()
                || call.arguments.keywords.len() != 1
                || call.arguments.keywords[0].arg.as_ref().map(|a| a.as_str()) != Some("level")
            {
                return Err(error(
                    call,
                    "expected @inductive or @inductive(level=level)",
                ));
            }
            Self::level(&call.arguments.keywords[0].value)?
        } else {
            0
        };
        let mut scope = Scope::default();
        let mut parameters = vec![];
        if let Some(params) = &class.type_params {
            for param in params.iter() {
                let ast::TypeParam::TypeVar(p) = param else {
                    return Err(error(
                        param,
                        "variadic inductive parameters are unsupported",
                    ));
                };
                if p.default.is_some() {
                    return Err(error(p, "default inductive parameters are unsupported"));
                }
                let bound = p
                    .bound
                    .as_deref()
                    .ok_or_else(|| error(p, "inductive parameter bound required"))?;
                let ty = self.expr(bound, &scope)?;
                self.bind(&mut scope, p.name.as_str(), p)?;
                parameters.push((p.name.to_string(), ty));
            }
        }
        let mut indices = vec![];
        let mut constructors_started = false;
        for stmt in &class.body {
            match stmt {
                Stmt::AnnAssign(index) if !constructors_started => {
                    let Expr::Name(name) = index.target.as_ref() else {
                        return Err(error(index, "index requires a name"));
                    };
                    let Expr::Subscript(annotation) = index.annotation.as_ref() else {
                        return Err(error(index, "expected Index[type]"));
                    };
                    if index.value.is_some()
                        || self.builtin(&annotation.value, &scope) != Some("Index")
                    {
                        return Err(error(index, "expected an index without a default"));
                    }
                    let ty = self.expr(&annotation.slice, &scope)?;
                    self.bind(&mut scope, name.id.as_str(), name)?;
                    indices.push((name.id.to_string(), ty));
                }
                Stmt::FunctionDef(_) => constructors_started = true,
                Stmt::Pass(_) => {}
                Stmt::Expr(e) if matches!(e.value.as_ref(), Expr::StringLiteral(_)) => {}
                _ => {
                    return Err(error(
                        stmt,
                        "inductive body requires indices followed by constructors",
                    ))
                }
            }
        }
        let name = self.qualified(class.name.as_str());
        self.globals.insert(
            class.name.to_string(),
            Binding {
                name: name.clone(),
                builtin: None,
                record: None,
                nullary: false,
                data: Some(DataBinding {
                    family: name.clone(),
                    constructors: vec![],
                    parameters: parameters.len(),
                    indices: indices.len(),
                    constructor: None,
                }),
            },
        );
        // Index binders describe the family signature; constructor fields bind
        // their own index witnesses, rather than capturing a class-level value.
        let mut parameter_scope = Scope::default();
        for (name, _) in &parameters {
            parameter_scope.locals.insert(name.clone());
        }
        let mut constructors = vec![];
        for stmt in &class.body {
            let Stmt::FunctionDef(f) = stmt else {
                continue;
            };
            self.tick(f.range())?;
            let valid_body = match f.body.as_slice() {
                [Stmt::Expr(e)] => matches!(e.value.as_ref(), Expr::EllipsisLiteral(_)),
                [Stmt::Expr(doc), Stmt::Expr(e)] => {
                    matches!(doc.value.as_ref(), Expr::StringLiteral(_))
                        && matches!(e.value.as_ref(), Expr::EllipsisLiteral(_))
                }
                _ => false,
            };
            if f.is_async
                || f.type_params.is_some()
                || f.decorator_list.len() != 1
                || self.builtin(&f.decorator_list[0].expression, &parameter_scope)
                    != Some("constructor")
                || !valid_body
            {
                return Err(error(
                    f,
                    "constructor requires @constructor, typed fields, and body ...",
                ));
            }
            self.parameters(&f.parameters)?;
            if !names.insert(f.name.to_string()) {
                return Err(error(f, "duplicate constructor or module binding"));
            }
            let mut scope = parameter_scope.clone();
            let mut fields = vec![];
            for param in f.parameters.posonlyargs.iter().chain(&f.parameters.args) {
                let p = &param.parameter;
                let annotation = p
                    .annotation
                    .as_deref()
                    .ok_or_else(|| error(p, "constructor field annotation required"))?;
                let ty = self.expr(annotation, &scope)?;
                self.bind(&mut scope, p.name.as_str(), p)?;
                fields.push((p.name.to_string(), ty));
            }
            let result = self.expr(
                f.returns
                    .as_deref()
                    .ok_or_else(|| error(f, "constructor result type required"))?,
                &scope,
            )?;
            let ctor_name = self.qualified(f.name.as_str());
            self.globals.insert(
                f.name.to_string(),
                Binding {
                    name: ctor_name.clone(),
                    builtin: None,
                    record: None,
                    nullary: fields.is_empty(),
                    data: Some(DataBinding {
                        family: name.clone(),
                        constructors: vec![],
                        parameters: parameters.len(),
                        indices: 0,
                        constructor: Some(constructors.len()),
                    }),
                },
            );
            constructors.push(deppy_elab::NamedConstructor {
                name: ctor_name,
                fields,
                result,
            });
        }
        let metadata = constructors
            .iter()
            .map(|c| (c.name.clone(), c.fields.len()))
            .collect::<Vec<_>>();
        for binding in self.globals.values_mut() {
            if let Some(data) = &mut binding.data {
                if data.family == name {
                    data.constructors = metadata.clone();
                }
            }
        }
        Ok(Declaration {
            name: name.clone(),
            span: class.range().into(),
            opaque: false,
            ty: E::Universe(level),
            body: DeclarationBody::Data(deppy_elab::NamedDataDecl {
                name,
                parameters,
                indices,
                constructors,
                level,
            }),
        })
    }
}
