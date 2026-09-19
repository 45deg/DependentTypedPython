use super::*;
impl Lowerer {
    pub(super) fn expr(&mut self, expr: &Expr, scope: &Scope) -> Result<E, Diagnostic> {
        self.tick(expr.range())?;
        Ok(match expr {
            Expr::Name(n) => {
                let name = n.id.as_str();
                if scope.locals.contains(name) {
                    E::name(name)
                } else if scope.assigned.contains(name) {
                    return Err(error(n, "local name used before its definition"));
                } else if let Some(builtin) = self.imports.get(name) {
                    match builtin.as_str() {
                        "Type" => E::Universe(0),
                        "Nat" => E::Nat,
                        "S" => E::lam("_n", Plicity::Explicit, Some(E::Nat), E::name("_n").succ()),
                        _ => {
                            return Err(error(
                                n,
                                "this deppy name requires supported call or subscript syntax",
                            ))
                        }
                    }
                } else if let Some(binding) = self.globals.get(name) {
                    E::name(&binding.name)
                } else {
                    return Err(error(n, format!("unknown or unchecked name: {name}")));
                }
            }
            Expr::Subscript(s) => {
                let args: Vec<&Expr> = match s.slice.as_ref() {
                    Expr::Tuple(t) => t.elts.iter().collect(),
                    e => vec![e],
                };
                if let Some(name) = self.record_name(&s.value, scope) {
                    if args.len() != self.records[&name].0 {
                        return Err(error(s, "wrong number of record type arguments"));
                    }
                }
                match self.builtin(&s.value, scope).map(str::to_owned).as_deref() {
                    Some("Type") if args.len() == 1 => {
                        let Expr::NumberLiteral(n) = args[0] else {
                            return Err(error(s, "universe level must be a concrete integer"));
                        };
                        let ast::Number::Int(level) = &n.value else {
                            return Err(error(n, "universe level must be a concrete integer"));
                        };
                        let level = level
                            .as_u64()
                            .and_then(|x| u32::try_from(x).ok())
                            .ok_or_else(|| error(n, "universe level overflows u32"))?;
                        E::Universe(level)
                    }
                    Some("Vec") if args.len() == 2 => {
                        E::vec(self.expr(args[0], scope)?, self.expr(args[1], scope)?)
                    }
                    Some("Fin") if args.len() == 1 => E::fin(self.expr(args[0], scope)?),
                    Some("Eq") if args.len() == 3 => E::eq(
                        self.expr(args[0], scope)?,
                        self.expr(args[1], scope)?,
                        self.expr(args[2], scope)?,
                    ),
                    Some(kind @ ("Pi" | "ImplicitPi" | "Sigma")) if args.len() == 2 => {
                        let kind = kind.to_owned();
                        let domain = self.expr(args[0], scope)?;
                        let Expr::Lambda(lambda) = args[1] else {
                            return Err(error(
                                args[1],
                                "dependent codomain must be a one-parameter lambda",
                            ));
                        };
                        let params = lambda
                            .parameters
                            .as_deref()
                            .ok_or_else(|| error(lambda, "codomain lambda needs one parameter"))?;
                        self.parameters(params)?;
                        let ps: Vec<_> = params.posonlyargs.iter().chain(&params.args).collect();
                        if ps.len() != 1 || ps[0].parameter.annotation.is_some() {
                            return Err(error(
                                params,
                                "codomain lambda needs one unannotated parameter",
                            ));
                        }
                        let name = ps[0].parameter.name.as_str();
                        let mut inner = scope.clone();
                        inner.locals.insert(name.into()); // lambda scope may shadow
                        let codomain = self.expr(&lambda.body, &inner)?;
                        if kind != "Sigma" {
                            E::pi(
                                name,
                                if kind == "ImplicitPi" {
                                    Plicity::Implicit
                                } else {
                                    Plicity::Explicit
                                },
                                domain,
                                codomain,
                            )
                        } else {
                            E::sigma(name, domain, codomain)
                        }
                    }
                    Some(_) => {
                        return Err(error(
                            s,
                            "unsupported type constructor or wrong number of arguments",
                        ))
                    }
                    None => {
                        let mut value = self.expr(&s.value, scope)?;
                        if args.is_empty() {
                            return Err(error(s, "explicit type argument list must not be empty"));
                        }
                        for arg in args {
                            value = value.implicit(self.expr(arg, scope)?);
                        }
                        value
                    }
                }
            }
            Expr::Call(call) => {
                if !call.arguments.keywords.is_empty() {
                    return Err(error(call, "keyword arguments are unsupported"));
                }
                if let (Some((name, implicit, arity)), Expr::Name(callee)) =
                    (&scope.recursion, call.func.as_ref())
                {
                    if callee.id.as_str() == name
                        && !scope.locals.contains(name)
                        && !scope.assigned.contains(name)
                    {
                        if call.arguments.args.len() != *arity {
                            return Err(error(
                                call,
                                "recursive call requires all explicit arguments",
                            ));
                        }
                        let mut args: Vec<E> = implicit.iter().map(E::name).collect();
                        for arg in &call.arguments.args {
                            args.push(self.expr(arg, scope)?);
                        }
                        return Ok(E::Recur(args));
                    }
                }
                if let Some(value) = self.record_call(call, scope)? {
                    return Ok(value);
                }
                let builtin = self.builtin(&call.func, scope).map(str::to_owned);
                if let Some(name @ ("J" | "nat_elim" | "vec_elim" | "fin_elim" | "record_elim")) =
                    builtin.as_deref()
                {
                    let raw = &call.arguments.args;
                    let count = match name {
                        "J" | "vec_elim" => 7,
                        "fin_elim" => 6,
                        "record_elim" => 4,
                        _ => 5,
                    };
                    if raw.len() != count {
                        return Err(error(call, "wrong number of eliminator arguments"));
                    }
                    let level = Self::level(&raw[0])?;
                    let args = raw[1..]
                        .iter()
                        .map(|a| self.expr(a, scope))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(match name {
                        "record_elim" => E::RecordElim {
                            level,
                            motive: Box::new(args[0].clone()),
                            branch: Box::new(args[1].clone()),
                            value: Box::new(args[2].clone()),
                        },
                        "J" => E::j(
                            level,
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                            args[3].clone(),
                            args[4].clone(),
                            args[5].clone(),
                        ),
                        "nat_elim" => E::nat_elim(
                            level,
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                            args[3].clone(),
                        ),
                        "vec_elim" => E::vec_elim(
                            level,
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                            args[3].clone(),
                            args[4].clone(),
                            args[5].clone(),
                        ),
                        _ => E::fin_elim(
                            level,
                            args[0].clone(),
                            args[1].clone(),
                            args[2].clone(),
                            args[3].clone(),
                            args[4].clone(),
                        ),
                    });
                }
                if let Some(name @ ("lam" | "implicit_lam")) = builtin.as_deref() {
                    if call.arguments.args.len() != 2 {
                        return Err(error(
                            call,
                            "lam expects a domain and a one-parameter lambda",
                        ));
                    }
                    let domain = self.expr(&call.arguments.args[0], scope)?;
                    let Expr::Lambda(lambda) = &call.arguments.args[1] else {
                        return Err(error(call, "lam expects a lambda"));
                    };
                    return self.lambda(
                        lambda,
                        scope,
                        Some(domain),
                        if name == "lam" {
                            Plicity::Explicit
                        } else {
                            Plicity::Implicit
                        },
                    );
                }
                let args = call
                    .arguments
                    .args
                    .iter()
                    .map(|arg| self.expr(arg, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                match (builtin.as_deref(), args.as_slice()) {
                    (Some("Z"), []) => E::Zero,
                    (Some("S"), [n]) => n.clone().succ(),
                    (Some("refl"), [n]) => n.clone().refl(),
                    (Some("ann"), [value, ty]) => value.clone().ann(ty.clone()),
                    (Some("vnil"), [ty]) => E::vnil(ty.clone()),
                    (Some("vcons"), [ty, len, head, tail]) => {
                        E::vcons(ty.clone(), len.clone(), head.clone(), tail.clone())
                    }
                    (Some("pair"), [ty, first, second]) => {
                        E::pair(first.clone(), second.clone()).ann(ty.clone())
                    }
                    (Some("fin0_elim"), [ty, absurd]) => E::fin0_elim(ty.clone(), absurd.clone()),
                    (Some("fin0_elim"), [absurd]) => {
                        E::fin0_elim(E::Hole.ann(E::Universe(0)), absurd.clone())
                    }
                    (Some("Pair"), [fst, snd]) => E::pair(fst.clone(), snd.clone()),
                    (Some("FZ"), [bound]) => E::fz(bound.clone()),
                    (Some("FS"), [bound, pred]) => E::fs(bound.clone(), pred.clone()),
                    (Some("VNil"), []) => E::lam(
                        "_A",
                        Plicity::Implicit,
                        Some(E::Universe(0)),
                        E::vnil(E::name("_A")),
                    )
                    .implicit(E::Hole),
                    (Some("VCons"), [k, head, tail]) => {
                        let a = E::name("_A");
                        E::lam(
                            "_A",
                            Plicity::Implicit,
                            Some(E::Universe(0)),
                            E::lam(
                                "_k",
                                Plicity::Explicit,
                                Some(E::Nat),
                                E::lam(
                                    "_h",
                                    Plicity::Explicit,
                                    Some(a.clone()),
                                    E::lam(
                                        "_t",
                                        Plicity::Explicit,
                                        Some(E::vec(a.clone(), E::name("_k"))),
                                        E::vcons(a, E::name("_k"), E::name("_h"), E::name("_t")),
                                    ),
                                ),
                            ),
                        )
                        .implicit(E::Hole)
                        .app(k.clone())
                        .app(head.clone())
                        .app(tail.clone())
                    }
                    (Some(_), _) => {
                        return Err(error(
                            call,
                            "unsupported builtin call or wrong number of arguments",
                        ))
                    }
                    (None, _) => {
                        if args.is_empty()
                            && !matches!(call.func.as_ref(), Expr::Name(n) if !scope.locals.contains(n.id.as_str()) && !scope.assigned.contains(n.id.as_str()) && self.globals.get(n.id.as_str()).is_some_and(|b| b.nullary))
                        {
                            return Err(error(
                                call,
                                "empty call requires a declared zero-parameter constant",
                            ));
                        }
                        let mut f = self.expr(&call.func, scope)?;
                        for arg in args {
                            f = f.app(arg);
                        }
                        f
                    }
                }
            }
            Expr::Lambda(lambda) => self.lambda(lambda, scope, None, Plicity::Explicit)?,
            Expr::Attribute(a) => {
                if matches!(a.value.as_ref(), Expr::Name(n) if n.id.as_str() == "self")
                    && !scope.fields.is_empty()
                    && !scope.locals.contains("self")
                {
                    if !scope.fields.contains(a.attr.as_str()) {
                        return Err(error(a, "self may only refer to preceding record fields"));
                    }
                    E::name(super::record::field_binding(a.attr.as_str()))
                } else {
                    let value = self.expr(&a.value, scope)?;
                    match a.attr.as_str() {
                        "fst" => value.fst(),
                        "snd" => value.snd(),
                        field => value.field(super::record::field_binding(field)),
                    }
                }
            }
            Expr::BinOp(b) if b.op == ast::Operator::Add => deppy_elab::prelude::nat_add()
                .app(self.expr(&b.left, scope)?)
                .app(self.expr(&b.right, scope)?),
            Expr::NumberLiteral(n) => {
                let ast::Number::Int(value) = &n.value else {
                    return Err(error(n, "only natural-number literals are supported"));
                };
                let value = value.as_u64().filter(|x| *x <= 1024).ok_or_else(|| {
                    error(n, "natural-number literal exceeds frontend limit (1024)")
                })?;
                (0..value).fold(E::Zero, |n, _| n.succ())
            }
            _ => return Err(error(expr, "unsupported dependent expression")),
        })
    }
}

impl Lowerer {
    fn lambda(
        &mut self,
        lambda: &ast::ExprLambda,
        scope: &Scope,
        domain: Option<E>,
        plicity: Plicity,
    ) -> Result<E, Diagnostic> {
        let params = lambda
            .parameters
            .as_deref()
            .ok_or_else(|| error(lambda, "lambda needs at least one parameter"))?;
        self.parameters(params)?;
        let params: Vec<_> = params.posonlyargs.iter().chain(&params.args).collect();
        if params.is_empty() || (domain.is_some() && params.len() != 1) {
            return Err(error(
                lambda,
                "annotated lambda needs exactly one parameter",
            ));
        }
        let mut inner = scope.clone();
        for p in &params {
            inner.locals.insert(p.parameter.name.to_string());
        }
        let mut body = self.expr(&lambda.body, &inner)?;
        for p in params.into_iter().rev() {
            body = E::lam(p.parameter.name.to_string(), plicity, domain.clone(), body);
        }
        Ok(body)
    }
}
