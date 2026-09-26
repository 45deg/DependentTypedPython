//! A single loop, interpreted by bounded iteration and a checked totality theorem.
use super::*;

pub(super) struct Loop<'a> {
    pub(super) id: usize,
    pub(super) annotation_names: Option<Vec<String>>,
    pub test: &'a Expr,
    pub body: Vec<Command<'a>>,
    pub(super) invariant: Option<&'a Expr>,
    pub(super) measure: &'a Expr,
    pub(super) names: Vec<String>,
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
pub(super) fn state_type(names: &[String], state: &State) -> E {
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

// Prefix proofs abstract contract results before checking the loop certificate.
enum PrefixProof {
    Let((String, E, E)),
    Call(Box<PrefixCall>),
}
struct PrefixCall {
    name: String,
    ty: E,
    actual: E,
    fact: String,
    fact_ty: E,
    evidence: E,
    pre: E,
    pre_proof: E,
}

fn prefix_proof(frames: Vec<PrefixProof>, mut goal: E, mut proof: E) -> E {
    for frame in frames.into_iter().rev() {
        match frame {
            PrefixProof::Let(binding) => {
                goal = lets(std::slice::from_ref(&binding), goal);
                proof = lets(&[binding], proof);
            }
            PrefixProof::Call(call) => {
                let PrefixCall {
                    name,
                    ty,
                    actual,
                    fact,
                    fact_ty,
                    evidence,
                    pre,
                    pre_proof,
                } = *call;
                let continuation_ty = E::pi(
                    &name,
                    Plicity::Explicit,
                    ty.clone(),
                    E::pi(&fact, Plicity::Explicit, fact_ty.clone(), goal.clone()),
                );
                proof = E::let_in(
                    "$prefix_pre",
                    Some(pre),
                    pre_proof,
                    lambda(&name, ty.clone(), lambda(&fact, fact_ty, proof))
                        .ann(continuation_ty)
                        .app(actual.clone())
                        .app(evidence.app(E::name("$prefix_pre"))),
                );
                goal = E::let_in(name, Some(ty), actual, goal);
            }
        }
    }
    proof
}

impl Lowerer {
    pub(super) fn loop_command<'a>(
        &mut self,
        w: &'a ast::StmtWhile,
    ) -> Result<Loop<'a>, Diagnostic> {
        if !w.orelse.is_empty() || w.body.len() < 2 {
            return Err(error(
                w,
                "while requires decreases and a body; while-else is unsupported",
            ));
        }
        let directive = |index: usize, builtin: &str| -> Option<&'a ast::ExprCall> {
            if let Stmt::Expr(e) = &w.body[index] {
                if let Expr::Call(c) = e.value.as_ref() {
                    if (self.builtin(&c.func, &Scope::default()) == Some(builtin)
                        || (builtin == "decreases"
                            && matches!(c.func.as_ref(), Expr::Name(n) if n.id.as_str() == "$range_decreases")))
                        && c.arguments.args.len() == 1
                    {
                        return Some(c);
                    }
                }
            }
            None
        };
        let invariant = directive(0, "invariant");
        let measure_index = usize::from(invariant.is_some());
        let measure = directive(measure_index, "decreases").ok_or_else(|| {
            error(
                &w.body[measure_index],
                "expected decreases(...) loop annotation",
            )
        })?;
        if !measure.arguments.keywords.is_empty() {
            return Err(error(measure, "decreases takes one positional measure"));
        }
        let mut names = vec![];
        if let Some(invariant) = invariant {
            if invariant.arguments.keywords.len() != 1 {
                return Err(error(invariant, "use invariant(predicate, state=(...))"));
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
            for item in &tuple.elts {
                let Expr::Name(n) = item else {
                    return Err(error(item, "loop state requires local names"));
                };
                if names.contains(&n.id.to_string()) {
                    return Err(error(item, "duplicate loop state name"));
                }
                names.push(n.id.to_string());
            }
        }
        let body = self.commands(&w.body[measure_index + 1..])?;
        if invariant.is_none() {
            // Stable source order, including both branches. Initialization is
            // checked below; inference never makes an unbound variable valid.
            fn writes(commands: &[Command<'_>], names: &mut Vec<String>) {
                for command in commands {
                    match command {
                        Command::Assign(name, _, _) => {
                            if !name.starts_with("$expr") && !names.iter().any(|n| n == name) {
                                names.push((*name).into());
                            }
                        }
                        Command::Parallel(bindings) => {
                            for (name, _) in bindings {
                                if !name.starts_with("$expr") && !names.iter().any(|n| n == name) {
                                    names.push((*name).into());
                                }
                            }
                        }
                        Command::While(inner) => {
                            for name in &inner.names {
                                if !name.starts_with("$expr") && !names.contains(name) {
                                    names.push(name.clone());
                                }
                            }
                        }
                        Command::If(_, yes, no) => {
                            writes(yes, names);
                            writes(no, names);
                        }
                        _ => {}
                    }
                }
            }
            writes(&body, &mut names);
        }
        let annotation_names = if matches!(&measure.arguments.args[0], Expr::Name(n) if n.id.as_str().starts_with("$expr_range_remaining"))
        {
            let original = names.clone();
            let Expr::Name(counter) = &measure.arguments.args[0] else {
                unreachable!()
            };
            let suffix = counter
                .id
                .as_str()
                .strip_prefix("$expr_range_remaining")
                .unwrap();
            for command in &body {
                if let Command::Assign(name, _, _) = command {
                    if (*name == counter.id.as_str()
                        || *name == format!("$expr_range_cursor{suffix}"))
                        && !names.iter().any(|n| n == name)
                    {
                        names.push((*name).into());
                    }
                }
            }
            Some(original)
        } else {
            None
        };
        Ok(Loop {
            annotation_names,
            id: 0,
            test: &w.test,
            body,
            invariant: invariant.map(|c| &c.arguments.args[0]),
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
                    if !name.starts_with("$expr") && !names.iter().any(|n| n == name) {
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
                if !name.starts_with("$expr") && !names.iter().any(|n| n == name) {
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
            Command::Assert(expr) => {
                self.value(expr, &state, Some(Scalar::Bool))?;
                if !state.allow_contracts {
                    return Err(error(
                        *expr,
                        "assert requires named or automatic verification",
                    ));
                }
                self.transition(rest, state, names, ty)
            }
            Command::Break(source) => Err(error(
                *source,
                "break requires named or automatic verification",
            )),
            Command::Continue(source) => Err(error(
                *source,
                "continue requires named or automatic verification",
            )),
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
                    let contract_call = if let Expr::Call(call) = expr {
                        if let Expr::Name(callee) = call.func.as_ref() {
                            self.globals
                                .get(callee.id.as_str())
                                .filter(|b| b.verified)
                                .cloned()
                                .map(|binding| (call, callee, binding))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let (Some((call, callee, binding)), Some(proofs)) =
                        (contract_call, named.as_mut())
                    {
                        if state.scope.assigned.contains(callee.id.as_str())
                            || state.scope.locals.contains(callee.id.as_str())
                        {
                            return Err(error(call, "verified local values are not callable"));
                        }
                        let contract = binding.contract.as_ref().unwrap();
                        if !call.arguments.keywords.is_empty()
                            || call.arguments.args.len() != contract.parameters.len()
                        {
                            return Err(error(
                                call,
                                "verified contract call requires the declared positional arguments",
                            ));
                        }
                        if state
                            .types
                            .get(*name)
                            .copied()
                            .or(*annotation)
                            .is_some_and(|s| s != contract.result)
                            || annotation.is_some_and(|s| s != contract.result)
                        {
                            return Err(error(call, "verified scalar type mismatch"));
                        }
                        let mut actual = E::name(&binding.name);
                        let mut evidence = E::name(specification_name(&binding.name));
                        let mut pre = contract.pre.clone();
                        let mut post = contract.post.clone();
                        for (argument, scalar) in
                            call.arguments.args.iter().zip(&contract.parameters)
                        {
                            let value = self.value(argument, &state, Some(*scalar))?.0;
                            actual = actual.app(value.clone());
                            evidence = evidence.app(value.clone());
                            pre = pre.app(value.clone());
                            post = post.app(value);
                        }
                        let key = proofs.call_key("", name);
                        let pre_proof =
                            self.obligation(proofs, &key, expr, &context, pre.clone())?;
                        let id = self.wildcard;
                        self.wildcard += 1;
                        let value = format!("$call_result{id}");
                        let fact = format!("$call_spec{id}");
                        let fact_ty = post.app(E::name(&value));
                        let ty = contract.result.expr();
                        state.scope.locals.insert((*name).into());
                        state.scope.aliases.insert((*name).into(), value.clone());
                        state.types.insert((*name).into(), contract.result);
                        context.push((value.clone(), ty.clone()));
                        context.push((fact.clone(), fact_ty.clone()));
                        prefix.push((value.clone(), ty.clone(), actual.clone()));
                        proof_prefix.push(PrefixProof::Call(Box::new(PrefixCall {
                            name: value,
                            ty,
                            actual,
                            fact,
                            fact_ty,
                            evidence,
                            pre,
                            pre_proof,
                        })));
                    } else {
                        let binding = self.loop_assign(name, *annotation, expr, &mut state)?;
                        prefix.push(binding.clone());
                        proof_prefix.push(PrefixProof::Let(binding));
                    }
                    if let Some(named) = &mut named {
                        proof_prefix.extend(
                            self.local_evidence(&[(name, expr)], &state, &mut context, "", named)?
                                .into_iter()
                                .map(PrefixProof::Let),
                        );
                    }
                }
                Command::Assert(source) => {
                    let value = self.value(source, &state, Some(Scalar::Bool))?.0;
                    let Some(proofs) = named.as_mut() else {
                        return Err(error(
                            *source,
                            "assert requires named or automatic verification",
                        ));
                    };
                    let goal = E::eq(Scalar::Bool.expr(), value, E::name("deppy.data.True_"));
                    let key = proofs.assertion_key("", source);
                    let proof = self.obligation(proofs, &key, source, &context, goal.clone())?;
                    let name = format!("$assert{}", self.wildcard);
                    self.wildcard += 1;
                    context.push((name.clone(), goal.clone()));
                    proof_prefix.push(PrefixProof::Let((name, goal, proof)));
                }
                Command::Parallel(bindings) => {
                    let lowered = self.parallel_values(bindings, &mut state)?;
                    prefix.extend(lowered.clone());
                    proof_prefix.extend(lowered.into_iter().map(PrefixProof::Let));
                    if let Some(named) = &mut named {
                        proof_prefix.extend(
                            self.local_evidence(bindings, &state, &mut context, "", named)?
                                .into_iter()
                                .map(PrefixProof::Let),
                        );
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
        let inv = if let Some(predicate) = loop_.invariant {
            let mut inv = self.expr(predicate, &state.scope)?.ann(inv_ty);
            for name in &loop_.names {
                inv = inv.app(E::name(&symbolic.scope.aliases[name]));
            }
            inv
        } else {
            let mut conditions = loop_
                .names
                .iter()
                .filter_map(|name| {
                    state.refinements.get(name).map(|predicate| {
                        predicate
                            .clone()
                            .app(E::name(&symbolic.scope.aliases[name]))
                    })
                })
                .collect::<Vec<_>>();
            let mut inv = conditions
                .pop()
                .unwrap_or_else(|| E::name("deppy.data.Unit"));
            for condition in conditions.into_iter().rev() {
                inv = E::sigma("$condition", condition, inv);
            }
            inv
        };
        let measure_is_value = matches!(loop_.measure, Expr::Name(name) if symbolic.types.contains_key(name.id.as_str()))
            || matches!(loop_.measure, Expr::NumberLiteral(_) | Expr::BinOp(_));
        let measure = if !measure_is_value
            && (matches!(loop_.measure, Expr::Lambda(_)) || loop_.invariant.is_some())
        {
            let mut measure = self.expr(loop_.measure, &state.scope)?.ann(measure_ty);
            for name in &loop_.names {
                measure = measure.app(E::name(&symbolic.scope.aliases[name]));
            }
            measure
        } else {
            self.value(loop_.measure, &symbolic, Some(Scalar::Nat))?.0
        };
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
        let arguments = [
            ty.clone(),
            guard.clone(),
            step.clone(),
            measure.clone(),
            inv.clone(),
            final_post.clone(),
            initial.clone(),
        ];
        let mut certificate = E::name("deppy.verified_loop.LoopVC");
        let mut correct = E::name("deppy.verified_loop.loop_correct");
        for arg in arguments {
            certificate = certificate.implicit(arg.clone());
            correct = correct.implicit(arg);
        }
        let witness = if let Some(mut named) = named {
            let init = self.obligation(
                &mut named,
                "loop.init",
                loop_.invariant.unwrap_or(loop_.test),
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
                    .map(|n| (n.as_str(), loop_.invariant.unwrap_or(loop_.test)))
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
                        split: None,
                        escape: None,
                        join: None,
                        source: if key == "loop.preserve" {
                            loop_.invariant.unwrap_or(loop_.test)
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
            let mut proof = prefix_proof(
                proof_prefix,
                certificate.clone(),
                E::pair(init, E::pair(preserve, E::pair(decrease, exit))),
            );
            for (name, ty) in context.into_iter().take(parameters.len() + 1).rev() {
                proof = lambda(&name, ty, proof);
            }
            proof
        } else {
            witness.unwrap()
        };
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
