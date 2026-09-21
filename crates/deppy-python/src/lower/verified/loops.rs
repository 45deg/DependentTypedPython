//! A single loop, interpreted by bounded iteration and a checked totality theorem.
use super::*;

pub(super) struct Loop<'a> {
    pub test: &'a Expr,
    pub body: Vec<Command<'a>>,
    invariant: &'a Expr,
    measure: &'a Expr,
    names: Vec<String>,
}
pub(super) fn contains_loop(commands: &[Command<'_>]) -> bool {
    commands.iter().any(|c| match c {
        Command::While(_) => true,
        Command::If(_, yes, no) => contains_loop(yes) || contains_loop(no),
        _ => false,
    })
}
fn lambda(name: &str, ty: E, body: E) -> E {
    E::lam(name, Plicity::Explicit, Some(ty), body)
}
pub(super) fn pack(names: &[String], state: &State) -> E {
    names
        .iter()
        .rev()
        .fold(E::name("deppy.data.MkUnit"), |tail, name| {
            E::pair(E::name(state.scope.aliases.get(name).unwrap_or(name)), tail)
        })
}
fn state_type(names: &[String], state: &State) -> E {
    names
        .iter()
        .rev()
        .fold(E::name("deppy.data.Unit"), |tail, name| {
            E::sigma("$field", state.types[name].expr(), tail)
        })
}
fn project(names: &[String], state: &State, value: E) -> (State, Vec<(String, E, E)>) {
    let mut state = state.clone();
    let mut bindings = vec![];
    let mut tail = value;
    for (i, name) in names.iter().enumerate() {
        let fresh = format!("$state_field{i}");
        bindings.push((fresh.clone(), state.types[name].expr(), tail.clone().fst()));
        state.scope.aliases.insert(name.clone(), fresh);
        tail = tail.snd();
    }
    (state, bindings)
}
pub(super) fn lets(bindings: &[(String, E, E)], mut body: E) -> E {
    for (name, ty, value) in bindings.iter().rev() {
        body = E::let_in(name, Some(ty.clone()), value.clone(), body);
    }
    body
}

impl Lowerer {
    pub(super) fn loop_command<'a>(
        &mut self,
        w: &'a ast::StmtWhile,
    ) -> Result<Loop<'a>, Diagnostic> {
        if !w.orelse.is_empty() || w.body.len() < 3 {
            return Err(error(
                w,
                "while requires invariant, decreases, and a body; while-else is unsupported",
            ));
        }
        let directive = |index: usize, builtin: &str| -> Result<&'a ast::ExprCall, Diagnostic> {
            if let Stmt::Expr(e) = &w.body[index] {
                if let Expr::Call(c) = e.value.as_ref() {
                    if self.builtin(&c.func, &Scope::default()) == Some(builtin)
                        && c.arguments.args.len() == 1
                    {
                        return Ok(c);
                    }
                }
            }
            Err(error(
                &w.body[index],
                format!("expected {builtin}(...) loop annotation"),
            ))
        };
        let invariant = directive(0, "invariant")?;
        let measure = directive(1, "decreases")?;
        if !measure.arguments.keywords.is_empty() || invariant.arguments.keywords.len() != 1 {
            return Err(error(
                w,
                "use invariant(predicate, state=(...)) and decreases(measure)",
            ));
        }
        let keyword = &invariant.arguments.keywords[0];
        if keyword.arg.as_ref().map(|s| s.as_str()) != Some("state") {
            return Err(error(keyword, "invariant requires state=(local, ...)"));
        }
        let Expr::Tuple(tuple) = &keyword.value else {
            return Err(error(
                keyword,
                "loop state must be a tuple of initialized local names",
            ));
        };
        let mut names = vec![];
        for item in &tuple.elts {
            let Expr::Name(n) = item else {
                return Err(error(item, "loop state requires local names"));
            };
            if names.contains(&n.id.to_string()) {
                return Err(error(item, "duplicate loop state name"));
            }
            names.push(n.id.to_string());
        }
        if names.is_empty() {
            return Err(error(tuple, "loop state must not be empty"));
        }
        Ok(Loop {
            test: &w.test,
            body: self.commands(&w.body[2..])?,
            invariant: &invariant.arguments.args[0],
            measure: &measure.arguments.args[0],
            names,
        })
    }

    pub(super) fn loop_assign(
        &mut self,
        name: &str,
        annotation: Option<Scalar>,
        expr: &Expr,
        state: &mut State,
    ) -> Result<(String, E, E), Diagnostic> {
        let old = state.types.get(name).copied();
        if old.is_some() && annotation.is_some() && old != annotation {
            return Err(error(
                expr,
                "verified reassignment cannot change a local's type",
            ));
        }
        let (value, ty) = self.value(expr, state, old.or(annotation))?;
        let fresh = format!("$verified{}", self.wildcard);
        self.wildcard += 1;
        state.scope.locals.insert(name.into());
        state.scope.aliases.insert(name.into(), fresh.clone());
        state.types.insert(name.into(), ty);
        Ok((fresh, ty.expr(), value))
    }

    fn transition(
        &mut self,
        commands: &[&Command<'_>],
        mut state: State,
        names: &[String],
        ty: &E,
    ) -> Result<E, Diagnostic> {
        let Some((command, rest)) = commands.split_first() else {
            return Ok(pack(names, &state).ann(ty.clone()));
        };
        match command {
            Command::Parallel(bindings) => {
                for (name, expr) in bindings {
                    if !names.iter().any(|n| n == name) {
                        return Err(error(
                            *expr,
                            "every loop assignment must target a declared state variable",
                        ));
                    }
                }
                let lowered = self.parallel_values(bindings, &mut state)?;
                Ok(lets(&lowered, self.transition(rest, state, names, ty)?))
            }
            Command::Assign(name, annotation, expr) => {
                if !names.iter().any(|n| n == name) {
                    return Err(error(
                        *expr,
                        "every loop assignment must target a declared state variable",
                    ));
                }
                let binding = self.loop_assign(name, *annotation, expr, &mut state)?;
                Ok(lets(&[binding], self.transition(rest, state, names, ty)?))
            }
            Command::If(test, yes, no) => {
                let guard = self.value(test, &state, Some(Scalar::Bool))?.0;
                let yes = yes.iter().chain(rest.iter().copied()).collect::<Vec<_>>();
                let no = no.iter().chain(rest.iter().copied()).collect::<Vec<_>>();
                let yes = self.transition(&yes, state.clone(), names, ty)?;
                let no = self.transition(&no, state, names, ty)?;
                Ok(E::name("deppy.verified.select")
                    .implicit(ty.clone())
                    .app(guard)
                    .app(no)
                    .app(yes))
            }
            Command::Refine(name, scalar, predicate) => {
                if !state.allow_contracts {
                    return Err(error(*predicate, "local Refined requires proofs="));
                }
                self.local_condition(name, *scalar, predicate, &mut state)?;
                self.transition(rest, state, names, ty)
            }
            Command::Return(expr) => Err(error(*expr, "return inside a loop is unsupported")),
            Command::While(loop_) => Err(error(loop_.test, "nested while is unsupported")),
        }
    }

    // The user supplies a LoopVC certificate. The generic checked library
    // theorem turns it into the same whole-function postcondition VC as before.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn verified_loop(
        &mut self,
        f: &ast::StmtFunctionDef,
        commands: &[Command<'_>],
        mut state: State,
        result: Scalar,
        parameters: Vec<(String, Scalar)>,
        pre: E,
        post: E,
        witness: Option<E>,
        mut named: Option<contracts::Proofs<'_>>,
    ) -> Result<Declaration, Diagnostic> {
        let position = commands
            .iter()
            .position(|c| matches!(c, Command::While(_)))
            .ok_or_else(|| error(f, "while must be a single top-level loop"))?;
        let Command::While(loop_) = &commands[position] else {
            unreachable!()
        };
        if contains_loop(&loop_.body) || contains_loop(&commands[position + 1..]) {
            return Err(error(f, "only one non-nested while is supported"));
        }
        let mut context = parameters
            .iter()
            .map(|(n, s)| (n.clone(), s.expr()))
            .collect::<Vec<_>>();
        context.push(("$pre".into(), pre.clone()));
        let mut prefix = vec![];
        let mut proof_prefix = vec![];
        for command in &commands[..position] {
            match command {
                Command::Refine(name, scalar, predicate) => {
                    if named.is_none() {
                        return Err(error(*predicate, "local Refined requires proofs="));
                    }
                    self.local_condition(name, *scalar, predicate, &mut state)?;
                }
                Command::Assign(name, annotation, expr) => {
                    let binding = self.loop_assign(name, *annotation, expr, &mut state)?;
                    prefix.push(binding.clone());
                    proof_prefix.push(binding);
                    if let Some(named) = &mut named {
                        proof_prefix.extend(self.local_evidence(
                            &[(name, expr)],
                            &state,
                            &mut context,
                            "",
                            named,
                        )?);
                    }
                }
                Command::Parallel(bindings) => {
                    let lowered = self.parallel_values(bindings, &mut state)?;
                    prefix.extend(lowered.clone());
                    proof_prefix.extend(lowered);
                    if let Some(named) = &mut named {
                        proof_prefix.extend(self.local_evidence(
                            bindings,
                            &state,
                            &mut context,
                            "",
                            named,
                        )?);
                    }
                }
                _ => return Err(error(f, "only assignments may precede while")),
            }
        }
        for name in &loop_.names {
            if !state.types.contains_key(name) {
                return Err(error(
                    loop_.test,
                    format!("loop state {name} must be initialized before while"),
                ));
            }
        }
        let ty = state_type(&loop_.names, &state);
        let initial = pack(&loop_.names, &state).ann(ty.clone());
        let (mut symbolic, fields) = project(&loop_.names, &state, E::name("$state"));
        let guard = lambda(
            "$state",
            ty.clone(),
            lets(
                &fields,
                self.value(loop_.test, &symbolic, Some(Scalar::Bool))?.0,
            ),
        );
        symbolic.allow_contracts = named.is_some();
        let next = self.transition(
            &loop_.body.iter().collect::<Vec<_>>(),
            symbolic.clone(),
            &loop_.names,
            &ty,
        )?;
        let step = lambda("$state", ty.clone(), lets(&fields, next));
        // Annotation functions capture the loop-entry environment; their explicit
        // arguments are the changing state components in the declared order.
        let mut inv_ty = E::Universe(0);
        let mut measure_ty = E::Nat;
        for name in loop_.names.iter().rev() {
            inv_ty = E::pi(name, Plicity::Explicit, state.types[name].expr(), inv_ty);
            measure_ty = E::pi(
                name,
                Plicity::Explicit,
                state.types[name].expr(),
                measure_ty,
            );
        }
        let mut inv = self.expr(loop_.invariant, &state.scope)?.ann(inv_ty);
        let mut measure = self.expr(loop_.measure, &state.scope)?.ann(measure_ty);
        for name in &loop_.names {
            let field = E::name(&symbolic.scope.aliases[name]);
            inv = inv.app(field.clone());
            measure = measure.app(field);
        }
        let inv = lambda("$state", ty.clone(), lets(&fields, inv));
        let measure = lambda("$state", ty.clone(), lets(&fields, measure));
        let after = self.denote(
            &commands[position + 1..].iter().collect::<Vec<_>>(),
            symbolic.clone(),
            result,
        )?;
        let finish = lambda("$state", ty.clone(), lets(&fields, after));
        let final_post = lambda(
            "$state",
            ty.clone(),
            post.clone().app(finish.clone().app(E::name("$state"))),
        );
        let end = E::name("deppy.verified_loop.iterate")
            .implicit(ty.clone())
            .app(guard.clone())
            .app(step.clone())
            .app(measure.clone().app(initial.clone()))
            .app(initial.clone());
        let denotation = lets(&prefix, finish.app(end));
        let witness = if let Some(mut named) = named {
            let init = self.obligation(
                &mut named,
                "loop.init",
                loop_.invariant,
                &context,
                inv.clone().app(initial.clone()),
            )?;
            let mut component = |key: &str, truth: bool| -> Result<E, Diagnostic> {
                let mut context = context.clone();
                let locals = vec![
                    ("$state".into(), ty.clone()),
                    ("$invariant".into(), inv.clone().app(E::name("$state"))),
                    (
                        "$test".into(),
                        E::eq(
                            Scalar::Bool.expr(),
                            guard.clone().app(E::name("$state")),
                            E::name(if truth {
                                "deppy.data.True_"
                            } else {
                                "deppy.data.False_"
                            }),
                        ),
                    ),
                ];
                context.extend(locals.clone());
                let entries = loop_
                    .names
                    .iter()
                    .map(|n| (n.as_str(), loop_.invariant))
                    .collect::<Vec<_>>();
                let facts = self.local_evidence(
                    &entries,
                    &symbolic,
                    &mut context,
                    &format!("{key}.entry."),
                    &mut named,
                )?;
                let proof = if truth {
                    let output_post = if key == "loop.preserve" {
                        inv.clone()
                    } else {
                        lambda(
                            "$next",
                            ty.clone(),
                            E::name("deppy.nat_order.LT")
                                .app(measure.clone().app(E::name("$next")))
                                .app(measure.clone().app(E::name("$state"))),
                        )
                    };
                    let completion = contracts::Completion {
                        names: &loop_.names,
                        ty: ty.clone(),
                        source: if key == "loop.preserve" {
                            loop_.invariant
                        } else {
                            loop_.measure
                        },
                    };
                    let (_, proof) = self.compose(
                        &loop_.body.iter().collect::<Vec<_>>(),
                        symbolic.clone(),
                        result,
                        &output_post,
                        &context,
                        &format!("{key}."),
                        &mut named,
                        Some(&completion),
                    )?;
                    proof
                } else {
                    // The exit continuation is also checked against contract-only results.
                    self.compose(
                        &commands[position + 1..].iter().collect::<Vec<_>>(),
                        symbolic.clone(),
                        result,
                        &post,
                        &context,
                        "loop.exit.",
                        &mut named,
                        None,
                    )?
                    .1
                };
                let mut proof = lets(&fields, lets(&facts, proof));
                for (name, ty) in locals.into_iter().rev() {
                    proof = lambda(&name, ty, proof);
                }
                Ok(proof)
            };
            let preserve = component("loop.preserve", true)?;
            let decrease = component("loop.decrease", true)?;
            let exit = component("loop.exit", false)?;
            named.finish()?;
            let mut proof = lets(
                &proof_prefix,
                E::pair(init, E::pair(preserve, E::pair(decrease, exit))),
            );
            for (name, ty) in context.into_iter().take(parameters.len() + 1).rev() {
                proof = lambda(&name, ty, proof);
            }
            proof
        } else {
            witness.unwrap()
        };
        let arguments = [ty, guard, step, measure, inv, final_post, initial];
        let mut certificate = E::name("deppy.verified_loop.LoopVC");
        let mut correct = E::name("deppy.verified_loop.loop_correct");
        for arg in arguments {
            certificate = certificate.implicit(arg.clone());
            correct = correct.implicit(arg);
        }
        certificate = lets(&prefix, certificate);
        let mut evidence = E::name("$loop_certificate");
        for (name, _) in &parameters {
            evidence = evidence.app(E::name(name));
        }
        evidence = evidence.app(E::name("$pre"));
        let correct = lets(&prefix, correct.app(evidence));
        let mut certificate_ty = E::pi("$pre", Plicity::Explicit, pre.clone(), certificate);
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
        let mut vc_ty = E::pi(
            "$pre",
            Plicity::Explicit,
            pre.clone(),
            post.app(denotation.clone()),
        );
        let mut vc = lambda("$pre", pre, correct);
        let mut body = denotation;
        let mut function_ty = result.expr();
        for (name, scalar) in parameters.into_iter().rev() {
            body = lambda(&name, scalar.expr(), body);
            vc = lambda(&name, scalar.expr(), vc);
            certificate_ty = E::pi(&name, Plicity::Explicit, scalar.expr(), certificate_ty);
            vc_ty = E::pi(&name, Plicity::Explicit, scalar.expr(), vc_ty);
            specification = E::pi(&name, Plicity::Explicit, scalar.expr(), specification);
            function_ty = E::pi(name, Plicity::Explicit, scalar.expr(), function_ty);
        }
        let body = E::let_in(
            "$loop_certificate",
            Some(certificate_ty),
            witness,
            E::let_in("$vc", Some(vc_ty), vc, body),
        );
        Ok(Declaration {
            opaque: false,
            name: self.qualified(f.name.as_str()),
            span: f.range.into(),
            ty: function_ty,
            body: DeclarationBody::Verified {
                proof: specification_proof(&body),
                implementation: body,
                specification,
            },
        })
    }
}
