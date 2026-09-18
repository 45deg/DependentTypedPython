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
                } else if self.globals.contains(name) {
                    E::name(name)
                } else {
                    return Err(error(n, format!("unknown or unchecked name: {name}")));
                }
            }
            Expr::Subscript(s) => {
                let args: Vec<&Expr> = match s.slice.as_ref() {
                    Expr::Tuple(t) => t.elts.iter().collect(),
                    e => vec![e],
                };
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
                    Some(kind @ ("Pi" | "Sigma")) if args.len() == 2 => {
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
                        if kind == "Pi" {
                            E::pi(name, Plicity::Explicit, domain, codomain)
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
                let builtin = self.builtin(&call.func, scope).map(str::to_owned);
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
                        if args.is_empty() {
                            return Err(error(call, "zero-argument user calls are not supported"));
                        }
                        let mut f = self.expr(&call.func, scope)?;
                        for arg in args {
                            f = f.app(arg);
                        }
                        f
                    }
                }
            }
            Expr::Attribute(a) => match a.attr.as_str() {
                "fst" => self.expr(&a.value, scope)?.fst(),
                "snd" => self.expr(&a.value, scope)?.snd(),
                _ => return Err(error(a, "only Sigma fst/snd projections are supported")),
            },
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
