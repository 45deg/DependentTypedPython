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
            if let Stmt::Match(s) = stmt {
                for case in &s.cases {
                    pattern(&case.pattern, names);
                    Self::capture_names(&case.body, names);
                }
            }
        }
    }

    pub(super) fn decorator(&self, f: &ast::StmtFunctionDef) -> Result<Option<String>, Diagnostic> {
        if f.decorator_list.len() != 1 {
            return Err(error(f, "expected one @dependent decorator"));
        }
        let expr = &f.decorator_list[0].expression;
        if self.builtin(expr, &Scope::default()) == Some("dependent") {
            return Ok(None);
        }
        if let Expr::Call(call) = expr {
            if self.builtin(&call.func, &Scope::default()) == Some("dependent")
                && call.arguments.args.is_empty()
                && call.arguments.keywords.len() == 1
            {
                let keyword = &call.arguments.keywords[0];
                if keyword.arg.as_ref().map(|a| a.as_str()) == Some("decreases") {
                    if let Expr::StringLiteral(value) = &keyword.value {
                        return Ok(Some(value.value.to_str().to_owned()));
                    }
                }
            }
        }
        Err(error(
            expr,
            "expected @dependent or @dependent(decreases=\"parameter\")",
        ))
    }

    pub(super) fn structural_body(
        &mut self,
        statements: &[Stmt],
        scope: &Scope,
    ) -> Result<Body, Diagnostic> {
        let [stmt] = statements else {
            return Err(Diagnostic {
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
