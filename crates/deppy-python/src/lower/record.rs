use super::*;

// These names cannot be spelled as identifiers in Python source.
pub(crate) fn constructor_name(record: &str) -> String {
    format!("$record:{record}:new")
}
pub(super) fn field_binding(field: &str) -> String {
    format!("$field:{field}")
}

impl Lowerer {
    pub(super) fn record_name(&self, value: &Expr, scope: &Scope) -> Option<String> {
        let Expr::Name(n) = value else {
            return None;
        };
        let name = n.id.as_str();
        (self.records.contains_key(name)
            && !scope.locals.contains(name)
            && !scope.assigned.contains(name))
        .then(|| name.to_owned())
    }

    pub(super) fn record_call(
        &mut self,
        call: &ast::ExprCall,
        scope: &Scope,
    ) -> Result<Option<E>, Diagnostic> {
        let (base, explicit) = match call.func.as_ref() {
            Expr::Subscript(s) => (s.value.as_ref(), Some(s.slice.as_ref())),
            e => (e, None),
        };
        let Some(name) = self.record_name(base, scope) else {
            return Ok(None);
        };
        let (params, fields) = self.records[&name];
        if call.arguments.args.len() != fields {
            return Err(error(call, "wrong number of record fields"));
        }
        let mut constructor = E::name(constructor_name(&name));
        if let Some(explicit) = explicit {
            let args: Vec<&Expr> = match explicit {
                Expr::Tuple(t) => t.elts.iter().collect(),
                e => vec![e],
            };
            if args.len() != params {
                return Err(error(call, "wrong number of record type arguments"));
            }
            for arg in args {
                constructor = constructor.implicit(self.expr(arg, scope)?);
            }
        } else {
            for _ in 0..params {
                constructor = constructor.implicit(E::Hole);
            }
        }
        for arg in &call.arguments.args {
            constructor = constructor.app(self.expr(arg, scope)?);
        }
        Ok(Some(constructor))
    }

    pub(super) fn record(&mut self, class: &ast::StmtClassDef) -> Result<Declaration, Diagnostic> {
        if class.decorator_list.len() != 1
            || self.builtin(&class.decorator_list[0].expression, &Scope::default())
                != Some("record")
        {
            return Err(error(
                class,
                "record class requires one bare @record decorator",
            ));
        }
        if class
            .arguments
            .as_ref()
            .is_some_and(|a| !a.args.is_empty() || !a.keywords.is_empty())
        {
            return Err(error(
                class,
                "record inheritance and metaclasses are unsupported",
            ));
        }
        let mut scope = Scope::default();
        let mut parameters = vec![];
        if let Some(params) = &class.type_params {
            for param in params.iter() {
                let ast::TypeParam::TypeVar(p) = param else {
                    return Err(error(param, "variadic record parameters are unsupported"));
                };
                if p.default.is_some() || p.name.as_str() == "self" {
                    return Err(error(p, "invalid record parameter"));
                }
                let bound = p
                    .bound
                    .as_deref()
                    .ok_or_else(|| error(p, "record parameter bound required"))?;
                let ty = self.expr(bound, &scope)?;
                self.bind(&mut scope, p.name.as_str(), p)?;
                parameters.push((p.name.to_string(), ty));
            }
        }
        let mut fields = vec![];
        for (i, stmt) in class.body.iter().enumerate() {
            self.tick(stmt.range())?;
            if matches!(stmt, Stmt::Expr(s) if i == 0 && matches!(s.value.as_ref(), Expr::StringLiteral(_)))
                || matches!(stmt, Stmt::Pass(_))
            {
                continue;
            }
            let Stmt::AnnAssign(field) = stmt else {
                return Err(error(
                    stmt,
                    "record body requires annotated fields without defaults",
                ));
            };
            let Expr::Name(name) = field.target.as_ref() else {
                return Err(error(field, "record field requires a name"));
            };
            let name = name.id.as_str();
            if field.value.is_some()
                || matches!(name, "self" | "fst" | "snd")
                || scope.locals.contains(name)
                || scope.fields.contains(name)
            {
                return Err(error(
                    field,
                    "duplicate, reserved, or defaulted record field",
                ));
            }
            let ty = self.expr(&field.annotation, &scope)?;
            fields.push((name.to_owned(), ty));
            scope.fields.insert(name.to_owned());
        }
        let name = class.name.to_string();
        let ty = parameters
            .iter()
            .rev()
            .fold(E::Universe(0), |result, (name, ty)| {
                E::pi(name, Plicity::Implicit, ty.clone(), result)
            });
        self.records
            .insert(name.clone(), (parameters.len(), fields.len()));
        let field_names = fields.iter().map(|(name, _)| name.clone()).collect();
        let fields = fields
            .into_iter()
            .map(|(name, ty)| (field_binding(&name), ty))
            .collect();
        Ok(Declaration {
            name,
            span: class.range.into(),
            ty,
            body: DeclarationBody::Record {
                declaration: deppy_elab::RecordDecl {
                    parameters,
                    fields,
                    level: 0,
                },
                field_names,
            },
        })
    }
}
