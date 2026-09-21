//! Verified command HIR and its total, pure denotation.
//!
//! Locals are immutable Core lets with fresh names. A branch denotes a Bool
//! eliminator, with the remaining commands interpreted in each branch's state.
//! WP(Q, c, s) = Q(denote(c, s)); the supplied proof is checked inside the same
//! Core definition as the denotation, never installed as an axiom.
//! A single while is handled by `loops` and checked stdlib totality theorems.
use super::*;
mod loops;

pub(crate) fn specification_name(function: &str) -> String {
    // Not a Python identifier, so source declarations cannot spoof this name.
    format!("$verified_spec:{function}")
}

fn specification_proof(body: &E) -> E {
    let E::Let {
        name,
        ty,
        value,
        body,
    } = body
    else {
        unreachable!("verified definitions contain a checked VC let")
    };
    E::let_in(
        name,
        ty.as_deref().cloned(),
        *value.clone(),
        if name == "$vc" {
            E::name(name)
        } else {
            specification_proof(body)
        },
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scalar {
    Nat,
    Bool,
}
impl Scalar {
    fn expr(self) -> E {
        match self {
            Self::Nat => E::Nat,
            Self::Bool => E::name("deppy.data.Bool"),
        }
    }
}

/// Expressions retain source AST until interpreted in a particular local state.
/// No host Python expressions or effects are evaluated.
enum Command<'a> {
    Assign(&'a str, Option<Scalar>, &'a Expr),
    If(&'a Expr, Vec<Command<'a>>, Vec<Command<'a>>),
    Return(&'a Expr),
    While(loops::Loop<'a>),
}
#[derive(Clone, Default)]
struct State {
    scope: Scope,
    types: HashMap<String, Scalar>,
}

impl Lowerer {
    fn scalar(&self, e: &Expr) -> Result<Scalar, Diagnostic> {
        if self.builtin(e, &Scope::default()) == Some("Nat") {
            return Ok(Scalar::Nat);
        }
        if let Expr::Name(n) = e {
            if self
                .globals
                .get(n.id.as_str())
                .is_some_and(|b| b.name == "deppy.data.Bool")
            {
                return Ok(Scalar::Bool);
            }
        }
        Err(error(e, "verified values require Nat or deppy.data.Bool"))
    }

    fn commands<'a>(&mut self, body: &'a [Stmt]) -> Result<Vec<Command<'a>>, Diagnostic> {
        let mut commands = vec![];
        for statement in body {
            self.tick(statement.range())?;
            commands.push(match statement {
                Stmt::Assign(a) if a.targets.len() == 1 => {
                    let Expr::Name(n) = &a.targets[0] else {
                        return Err(error(a, "verified assignment requires one local name"));
                    };
                    Command::Assign(n.id.as_str(), None, &a.value)
                }
                Stmt::AnnAssign(a) => {
                    let Expr::Name(n) = a.target.as_ref() else {
                        return Err(error(a, "verified assignment requires one local name"));
                    };
                    Command::Assign(
                        n.id.as_str(),
                        Some(self.scalar(&a.annotation)?),
                        a.value
                            .as_deref()
                            .ok_or_else(|| error(a, "verified local requires a value"))?,
                    )
                }
                Stmt::If(branch) => {
                    let mut otherwise = vec![];
                    for clause in branch.elif_else_clauses.iter().rev() {
                        let body = self.commands(&clause.body)?;
                        otherwise = if let Some(test) = &clause.test {
                            vec![Command::If(test, body, otherwise)]
                        } else {
                            body
                        };
                    }
                    Command::If(&branch.test, self.commands(&branch.body)?, otherwise)
                }
                Stmt::While(w) => Command::While(self.loop_command(w)?),
                Stmt::Return(r) => Command::Return(
                    r.value
                        .as_deref()
                        .ok_or_else(|| error(r, "verified return requires a value"))?,
                ),
                _ => {
                    return Err(error(
                        statement,
                        "verified supports local assignment, if, while, and return",
                    ))
                }
            });
        }
        Ok(commands)
    }

    fn value(
        &mut self,
        e: &Expr,
        state: &State,
        expected: Option<Scalar>,
    ) -> Result<(E, Scalar), Diagnostic> {
        self.tick(e.range())?;
        let (term, ty) = match e {
            Expr::BooleanLiteral(b) => (
                E::name(if b.value {
                    "deppy.data.True_"
                } else {
                    "deppy.data.False_"
                }),
                Scalar::Bool,
            ),
            Expr::NumberLiteral(_) => (self.expr(e, &state.scope)?, Scalar::Nat),
            Expr::Name(n) => {
                let ty = state
                    .types
                    .get(n.id.as_str())
                    .copied()
                    .ok_or_else(|| error(n, "verified value must be an initialized local"))?;
                (self.expr(e, &state.scope)?, ty)
            }
            Expr::BinOp(b) => {
                let name = match b.op {
                    ast::Operator::Add => "deppy.nat.add",
                    ast::Operator::Mult => "deppy.nat.mul",
                    _ => return Err(error(b, "verified arithmetic supports + and * on Nat")),
                };
                let left = self.value(&b.left, state, Some(Scalar::Nat))?.0;
                let right = self.value(&b.right, state, Some(Scalar::Nat))?.0;
                (E::name(name).app(left).app(right), Scalar::Nat)
            }
            Expr::Compare(c) if c.ops.len() == 1 && c.comparators.len() == 1 => {
                let name = match c.ops[0] {
                    ast::CmpOp::Lt => "deppy.verified.nat_lt",
                    ast::CmpOp::LtE => "deppy.verified.nat_le",
                    _ => return Err(error(c, "verified comparisons support < and <= on Nat")),
                };
                let left = self.value(&c.left, state, Some(Scalar::Nat))?.0;
                let right = self.value(&c.comparators[0], state, Some(Scalar::Nat))?.0;
                (E::name(name).app(left).app(right), Scalar::Bool)
            }
            Expr::Call(c) => {
                // Calls are only to already checked pure definitions, never host
                // functions, locals, recursive self calls or Python attributes.
                let Expr::Name(n) = c.func.as_ref() else {
                    return Err(error(c, "verified calls require a checked function name"));
                };
                if state.scope.locals.contains(n.id.as_str())
                    || state.scope.assigned.contains(n.id.as_str())
                {
                    return Err(error(c, "verified local values are not callable"));
                }
                if !self.globals.contains_key(n.id.as_str())
                    && self.builtin(&c.func, &state.scope) != Some("S")
                {
                    return Err(error(c, "verified calls require a checked pure function"));
                }
                if !c.arguments.keywords.is_empty() {
                    return Err(error(c, "verified pure calls require positional arguments"));
                }
                let mut term = self.expr(&c.func, &state.scope)?;
                for argument in &c.arguments.args {
                    term = term.app(self.value(argument, state, None)?.0);
                }
                (term, expected.unwrap_or(Scalar::Nat))
            }
            _ => return Err(error(e, "unsupported verified value expression")),
        };
        if expected.is_some_and(|expected| expected != ty) {
            return Err(error(e, "verified scalar type mismatch"));
        }
        // In particular, check the declared result type of every pure call.
        Ok((term.ann(ty.expr()), ty))
    }

    fn denote(
        &mut self,
        commands: &[&Command<'_>],
        mut state: State,
        result: Scalar,
    ) -> Result<E, Diagnostic> {
        let Some((command, rest)) = commands.split_first() else {
            return Err(Diagnostic {
                details: Default::default(),
                span: crate::Span { start: 0, end: 0 },
                message: "every verified path must return a value".into(),
            });
        };
        match command {
            Command::While(loop_) => {
                Err(error(loop_.test, "while must be a single top-level loop"))
            }
            Command::Return(e) => self.value(e, &state, Some(result)).map(|(term, _)| term),
            Command::Assign(name, annotation, e) => {
                let old = state.types.get(*name).copied();
                if old.is_some() && annotation.is_some() && old != *annotation {
                    return Err(error(
                        *e,
                        "verified reassignment cannot change a local's type",
                    ));
                }
                let (value, ty) = self.value(e, &state, old.or(*annotation))?;
                let fresh = format!("$verified{}", self.wildcard);
                self.wildcard += 1;
                state.scope.locals.insert((*name).into());
                state.scope.aliases.insert((*name).into(), fresh.clone());
                state.types.insert((*name).into(), ty);
                let body = self.denote(rest, state, result)?;
                Ok(E::let_in(fresh, Some(ty.expr()), value, body))
            }
            Command::If(test, yes, no) => {
                let value = self.value(test, &state, Some(Scalar::Bool))?.0;
                let yes = yes.iter().chain(rest.iter().copied()).collect::<Vec<_>>();
                let no = no.iter().chain(rest.iter().copied()).collect::<Vec<_>>();
                let yes = self.denote(&yes, state.clone(), result)?;
                let no = self.denote(&no, state, result)?;
                Ok(E::Induct {
                    level: 0,
                    value: Box::new(value),
                    motive: Box::new(E::lam(
                        "$condition",
                        Plicity::Explicit,
                        Some(Scalar::Bool.expr()),
                        result.expr(),
                    )),
                    branches: vec![no, yes],
                })
            }
        }
    }

    pub(super) fn verified(&mut self, f: &ast::StmtFunctionDef) -> Result<Declaration, Diagnostic> {
        if f.is_async || f.type_params.is_some() || f.decorator_list.len() != 1 {
            return Err(error(
                f,
                "verified requires one decorator, no async or type parameters",
            ));
        }
        self.parameters(&f.parameters)?;
        let Expr::Call(decorator) = &f.decorator_list[0].expression else {
            return Err(error(
                f,
                "use @verified(ensures=..., proof=..., requires=...)",
            ));
        };
        if !decorator.arguments.args.is_empty() {
            return Err(error(decorator, "verified options must be named"));
        }
        let mut options = HashMap::new();
        for keyword in &decorator.arguments.keywords {
            let name = keyword.arg.as_ref().map(|n| n.as_str()).unwrap_or("");
            if !matches!(name, "requires" | "ensures" | "proof")
                || options.insert(name, &keyword.value).is_some()
            {
                return Err(error(keyword, "unknown or duplicate verified option"));
            }
        }
        let ensures = options
            .get("ensures")
            .ok_or_else(|| error(f, "verified requires ensures"))?;
        let proof = options
            .get("proof")
            .ok_or_else(|| error(f, "verified requires proof (use hole to inspect the VC)"))?;
        let outer = Scope::default();
        let mut post = self.expr(ensures, &outer)?;
        let witness = self.expr(proof, &outer)?;
        let mut pre = options
            .get("requires")
            .map(|e| self.expr(e, &outer))
            .transpose()?;
        let mut state = State::default();
        let mut parameters = vec![];
        for parameter in f.parameters.posonlyargs.iter().chain(&f.parameters.args) {
            let p = &parameter.parameter;
            let ty = self.scalar(
                p.annotation
                    .as_deref()
                    .ok_or_else(|| error(p, "verified parameter annotation required"))?,
            )?;
            let name = p.name.to_string();
            self.bind(&mut state.scope, &name, p)?;
            state.types.insert(name.clone(), ty);

            parameters.push((name, ty));
        }
        let result = self.scalar(
            f.returns
                .as_deref()
                .ok_or_else(|| error(f, "verified return annotation required"))?,
        )?;
        let body = if matches!(f.body.first(), Some(Stmt::Expr(e)) if matches!(e.value.as_ref(), Expr::StringLiteral(_)))
        {
            &f.body[1..]
        } else {
            &f.body[..]
        };
        let commands = self.commands(body)?;
        fn capture(commands: &[Command<'_>], assigned: &mut HashSet<String>) {
            for c in commands {
                match c {
                    Command::Assign(name, _, _) => {
                        assigned.insert((*name).into());
                    }
                    Command::If(_, yes, no) => {
                        capture(yes, assigned);
                        capture(no, assigned);
                    }
                    Command::While(loop_) => capture(&loop_.body, assigned),
                    Command::Return(_) => {}
                }
            }
        }
        capture(&commands, &mut state.scope.assigned);

        let mut post_ty = E::pi("$result", Plicity::Explicit, result.expr(), E::Universe(0));
        let mut pre_ty = E::Universe(0);
        for (name, scalar) in parameters.iter().rev() {
            post_ty = E::pi(name, Plicity::Explicit, scalar.expr(), post_ty);
            pre_ty = E::pi(name, Plicity::Explicit, scalar.expr(), pre_ty);
        }
        post = post.ann(post_ty);
        pre = pre.map(|pre| pre.ann(pre_ty));
        for (name, _) in &parameters {
            post = post.app(E::name(name));
            pre = pre.map(|pre| pre.app(E::name(name)));
        }
        let pre = pre.unwrap_or_else(|| E::name("deppy.data.Unit"));
        if loops::contains_loop(&commands) {
            return self.verified_loop(f, &commands, state, result, parameters, pre, post, witness);
        }
        let denotation = self.denote(&commands.iter().collect::<Vec<_>>(), state, result)?;
        let mut call = E::name(self.qualified(f.name.as_str()));
        for (name, _) in &parameters {
            call = call.app(E::name(name));
        }
        let mut specification = E::pi(
            "$pre",
            Plicity::Explicit,
            pre.clone(),
            post.clone().app(call),
        );
        let mut vc = E::pi("$pre", Plicity::Explicit, pre, post.app(denotation.clone()));
        let mut body = denotation;
        let mut ty = result.expr();
        for (name, scalar) in parameters.into_iter().rev() {
            body = E::lam(&name, Plicity::Explicit, Some(scalar.expr()), body);
            vc = E::pi(&name, Plicity::Explicit, scalar.expr(), vc);
            specification = E::pi(&name, Plicity::Explicit, scalar.expr(), specification);
            ty = E::pi(name, Plicity::Explicit, scalar.expr(), ty);
        }
        body = E::let_in("$vc", Some(vc), witness, body);
        Ok(Declaration {
            opaque: false,
            name: self.qualified(f.name.as_str()),
            span: f.range.into(),
            ty,
            body: DeclarationBody::Verified {
                proof: specification_proof(&body),
                implementation: body,
                specification,
            },
        })
    }
}
