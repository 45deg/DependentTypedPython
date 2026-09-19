use super::*;
use deppy_elab::lower::{Arm, Body, Pattern};

impl Lowerer {
    pub(super) fn capture_names(statements: &[Stmt], names: &mut HashSet<String>) {
        fn pattern(p: &ast::Pattern, names: &mut HashSet<String>) {
            match p {
                ast::Pattern::MatchAs(p) => {
                    if let Some(n) = &p.name {
                        names.insert(n.to_string());
                    }
                }
                ast::Pattern::MatchClass(p) => {
                    for p in &p.arguments.patterns {
                        pattern(p, names);
                    }
                }
                _ => {}
            }
        }
        for stmt in statements {
            let target = match stmt {
                Stmt::Assign(s) if s.targets.len() == 1 => Some(&s.targets[0]),
                Stmt::AnnAssign(s) => Some(s.target.as_ref()),
                _ => None,
            };
            if let Some(Expr::Name(name)) = target {
                names.insert(name.id.to_string());
            }
            if let Stmt::Match(s) = stmt {
                for case in &s.cases {
                    pattern(&case.pattern, names);
                    Self::capture_names(&case.body, names);
                }
            }
        }
    }

    pub(super) fn level(expr: &Expr) -> Result<u32, Diagnostic> {
        if let Expr::NumberLiteral(n) = expr {
            if let ast::Number::Int(value) = &n.value {
                if let Some(level) = value.as_u64().and_then(|n| u32::try_from(n).ok()) {
                    return Ok(level);
                }
            }
        }
        Err(error(
            expr,
            "universe level requires a nonnegative u32 integer literal",
        ))
    }

    pub(super) fn decorator(
        &self,
        f: &ast::StmtFunctionDef,
    ) -> Result<(Option<(String, u32)>, bool), Diagnostic> {
        if f.decorator_list.len() != 1 {
            return Err(error(f, "expected one @dependent decorator"));
        }
        let expr = &f.decorator_list[0].expression;
        if self.builtin(expr, &Scope::default()) == Some("dependent") {
            return Ok((None, false));
        }
        if let Expr::Call(call) = expr {
            if self.builtin(&call.func, &Scope::default()) == Some("dependent")
                && call.arguments.args.is_empty()
            {
                let mut decreases = None;
                let mut level = None;
                let mut opaque = None;
                for keyword in &call.arguments.keywords {
                    match keyword.arg.as_ref().map(|a| a.as_str()) {
                        Some("opaque") if opaque.is_none() => {
                            let Expr::BooleanLiteral(value) = &keyword.value else {
                                return Err(error(keyword, "opaque requires a boolean literal"));
                            };
                            opaque = Some(value.value);
                        }
                        Some("decreases") if decreases.is_none() => {
                            let Expr::StringLiteral(value) = &keyword.value else {
                                return Err(error(
                                    keyword,
                                    "decreases requires a parameter name string",
                                ));
                            };
                            decreases = Some(value.value.to_str().to_owned());
                        }
                        Some("motive_level") if level.is_none() => {
                            level = Some(Self::level(&keyword.value)?);
                        }
                        _ => return Err(error(keyword, "unknown or duplicate dependent option")),
                    }
                }
                if let Some(name) = decreases {
                    return Ok((Some((name, level.unwrap_or(0))), opaque.unwrap_or(false)));
                }
                if let (Some(opaque), None) = (opaque, level) {
                    return Ok((None, opaque));
                }
            }
        }
        Err(error(
            expr,
            "expected @dependent or @dependent(decreases=parameter, motive_level=level, opaque=boolean)",
        ))
    }

    pub(super) fn structural_body(
        &mut self,
        statements: &[Stmt],
        scope: &Scope,
    ) -> Result<Body, Diagnostic> {
        if let Some((Stmt::Return(ret), prefix)) = statements.split_last() {
            let mut scope = scope.clone();
            let mut lets = vec![];
            for stmt in prefix {
                self.tick(stmt.range())?;
                let (target, annotation, value) = match stmt {
                    Stmt::Assign(s) if s.targets.len() == 1 => {
                        (&s.targets[0], None, s.value.as_ref())
                    }
                    Stmt::AnnAssign(s) => (
                        s.target.as_ref(),
                        Some(s.annotation.as_ref()),
                        s.value
                            .as_deref()
                            .ok_or_else(|| error(s, "local definition requires a value"))?,
                    ),
                    _ => {
                        return Err(error(
                            stmt,
                            "expected immutable local definitions before return",
                        ))
                    }
                };
                let Expr::Name(name) = target else {
                    return Err(error(target, "assignment requires a single local name"));
                };
                let ty = annotation.map(|ty| self.expr(ty, &scope)).transpose()?;
                let value = self.expr(value, &scope)?;
                self.bind(&mut scope, name.id.as_str(), name)?;
                lets.push((name.id.to_string(), ty, value));
            }
            let mut result = self.expr(
                ret.value
                    .as_deref()
                    .ok_or_else(|| error(ret, "return value required"))?,
                &scope,
            )?;
            for (name, ty, value) in lets.into_iter().rev() {
                result = E::let_in(name, ty, value, result);
            }
            return Ok(Body::Return(result));
        }
        if statements.len() > 1 && matches!(statements.last(), Some(Stmt::Match(_))) {
            let (last, prefix) = statements.split_last().unwrap();
            let mut inner = scope.clone();
            let mut locals = vec![];
            for stmt in prefix {
                self.tick(stmt.range())?;
                let (target, annotation, value) = match stmt {
                    Stmt::Assign(s) if s.targets.len() == 1 => {
                        (&s.targets[0], None, s.value.as_ref())
                    }
                    Stmt::AnnAssign(s) => (
                        s.target.as_ref(),
                        Some(s.annotation.as_ref()),
                        s.value
                            .as_deref()
                            .ok_or_else(|| error(s, "local definition requires a value"))?,
                    ),
                    _ => {
                        return Err(error(
                            stmt,
                            "expected immutable local definitions before match",
                        ))
                    }
                };
                let Expr::Name(name) = target else {
                    return Err(error(target, "assignment requires a single local name"));
                };
                let ty = annotation.map(|ty| self.expr(ty, &inner)).transpose()?;
                let value = self.expr(value, &inner)?;
                self.bind(&mut inner, name.id.as_str(), name)?;
                locals.push((name.id.to_string(), ty, value));
            }
            let body = self.structural_body(std::slice::from_ref(last), &inner)?;
            return Ok(locals
                .into_iter()
                .rev()
                .fold(body, |body, (name, ty, value)| Body::Let {
                    name,
                    ty,
                    value,
                    body: Box::new(body),
                }));
        }
        let [stmt] = statements else {
            return Err(Diagnostic {
                details: Default::default(),
                span: statements
                    .first()
                    .map(|s| s.range().into())
                    .unwrap_or(crate::Span { start: 0, end: 0 }),
                message: "structural body requires exactly one match or return".into(),
            });
        };
        self.tick(stmt.range())?;
        match stmt {
            Stmt::Return(s) => Ok(Body::Return(
                self.expr(
                    s.value
                        .as_deref()
                        .ok_or_else(|| error(s, "return value required"))?,
                    scope,
                )?,
            )),
            Stmt::Match(s) => {
                let Expr::Name(subject) = s.subject.as_ref() else {
                    return Err(error(s, "match subject must be a parameter name"));
                };
                let mut arms = vec![];
                for case in &s.cases {
                    if case.guard.is_some() {
                        return Err(error(case, "match guards are unsupported"));
                    }
                    let mut inner = scope.clone();
                    let pattern = self.pattern(&case.pattern, &mut inner)?;
                    arms.push(Arm {
                        pattern,
                        body: self.structural_body(&case.body, &inner)?,
                    });
                }
                Ok(Body::Match {
                    scrutinee: subject.id.to_string(),
                    arms,
                })
            }
            _ => Err(error(stmt, "structural body requires match or return")),
        }
    }

    fn pattern(
        &mut self,
        pattern: &ast::Pattern,
        scope: &mut Scope,
    ) -> Result<Pattern, Diagnostic> {
        self.tick(pattern.range())?;
        let ast::Pattern::MatchClass(class) = pattern else {
            return Err(error(pattern, "expected a constructor pattern"));
        };
        let kind = self.builtin(&class.cls, scope).unwrap_or("").to_owned();
        if !class.arguments.keywords.is_empty() {
            return Err(error(pattern, "keyword patterns are unsupported"));
        }
        let mut names = vec![];
        for p in &class.arguments.patterns {
            let ast::Pattern::MatchAs(capture) = p else {
                return Err(error(p, "expected a simple capture name"));
            };
            if capture.pattern.is_some() {
                return Err(error(p, "nested constructor patterns are unsupported"));
            }
            if let Some(name) = &capture.name {
                self.bind(scope, name.as_str(), name)?;
                names.push(name.to_string());
            } else if matches!(kind.as_str(), "FZ" | "FS") && names.is_empty() {
                // '$' cannot occur in Python identifiers, but is a valid HIR name.
                names.push(format!("$wild{}", self.wildcard));
                self.wildcard += 1;
            } else {
                return Err(error(
                    p,
                    "only Fin bound witnesses may use wildcard captures",
                ));
            }
        }
        Ok(match (kind.as_str(), names.as_slice()) {
            ("Z", []) => Pattern::Zero,
            ("S", [n]) => Pattern::Succ(n.clone()),
            ("VNil", []) => Pattern::VNil,
            ("VCons", [len, head, tail]) => Pattern::VCons {
                len: len.clone(),
                head: head.clone(),
                tail: tail.clone(),
            },
            ("FZ", [n]) => Pattern::FZ(n.clone()),
            ("FS", [bound, pred]) => Pattern::FS {
                bound: bound.clone(),
                pred: pred.clone(),
            },
            _ => return Err(error(pattern, "unsupported constructor pattern or arity")),
        })
    }
}
