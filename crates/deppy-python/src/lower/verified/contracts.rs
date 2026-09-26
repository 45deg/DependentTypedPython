//! Modular call proofs. A continuation is checked for every result satisfying
//! the callee's contract, then instantiated using its checked companion theorem.
use super::*;
mod proofs;
pub(super) use proofs::Proofs;

#[derive(Clone, Debug)]
pub(crate) struct Contract {
    pub(super) parameters: Vec<Scalar>,
    pub(super) result: Scalar,
    pub(super) pre: E,
    pub(super) post: E,
}
impl Contract {
    pub(crate) fn from_declaration(declaration: &Declaration) -> Option<Self> {
        let DeclarationBody::Verified { specification, .. } = &declaration.body else {
            return None;
        };
        let mut ty = &declaration.ty;
        let mut spec = specification;
        let mut parameters = vec![];
        let scalar = |ty: &E| match ty {
            E::Nat => Scalar::Nat,
            E::Name(n) if n == "deppy.integer.Int" => Scalar::Int,
            E::Name(n) if n == "deppy.data.Bool" => Scalar::Bool,
            _ => unreachable!("verified signature has scalar types"),
        };
        while let E::Pi {
            name,
            domain,
            codomain,
            ..
        } = ty
        {
            parameters.push((name.clone(), scalar(domain)));
            ty = codomain;
            let E::Pi { codomain, .. } = spec else {
                unreachable!()
            };
            spec = codomain;
        }
        let E::Pi {
            domain, codomain, ..
        } = spec
        else {
            unreachable!()
        };
        let E::App { function, .. } = codomain.as_ref() else {
            unreachable!()
        };
        let mut pre = *domain.clone();
        let mut post = *function.clone();
        for (name, scalar) in parameters.iter().rev() {
            pre = E::lam(name, Plicity::Explicit, Some(scalar.expr()), pre);
            post = E::lam(name, Plicity::Explicit, Some(scalar.expr()), post);
        }
        Some(Self {
            parameters: parameters.into_iter().map(|(_, s)| s).collect(),
            result: scalar(ty),
            pre,
            post,
        })
    }
}

pub(super) struct Completion<'a> {
    pub names: &'a [String],
    pub ty: E,
    pub source: &'a Expr,
    pub split: Option<[(E, &'a Expr); 2]>,
    pub escape: Option<Escape<'a>>,
    pub join: Option<Join<'a>>,
}
pub(super) struct Join<'a> {
    pub trivial: bool,
    pub rest: Vec<&'a Command<'a>>,
    pub post: E,
    pub parent: Option<&'a Completion<'a>>,
}
pub(super) struct Escape<'a> {
    pub rest: Vec<&'a Command<'a>>,
    pub parent: Option<&'a Completion<'a>>,
    pub post: E,
    pub output: E,
    pub return_post: E,
    pub wrappers: Vec<(E, E)>,
}
impl Completion<'_> {
    pub fn output_type(&self) -> E {
        self.escape.as_ref().map_or_else(
            || self.ty.clone(),
            |e| sum_type(self.ty.clone(), e.output.clone()),
        )
    }
}
// Keep the result behind a product boundary, including when it is itself a
// surrounding loop control value. It is payload, never a recursive control edge.
pub(super) fn sum_type(left: E, right: E) -> E {
    E::name("deppy.data.Sum").implicit(left).implicit(E::sigma(
        "$result",
        right,
        E::name("deppy.data.Unit"),
    ))
}
pub(super) fn outcome(left: bool, a: E, b: E, value: E) -> E {
    E::name(if left {
        "deppy.data.Left"
    } else {
        "deppy.data.Right"
    })
    .implicit(a)
    .implicit(E::sigma("$result", b, E::name("deppy.data.Unit")))
    .app(if left {
        value
    } else {
        E::pair(value, E::name("deppy.data.MkUnit"))
    })
}
impl Lowerer {
    #[allow(clippy::too_many_arguments)]
    fn return_evidence(
        &mut self,
        mut value: E,
        source: &Expr,
        post: &E,
        context: &[(String, E)],
        path: &str,
        proofs: &mut Proofs<'_>,
        completion: Option<&Completion<'_>>,
    ) -> Result<(E, E), Diagnostic> {
        let escape = completion.and_then(|end| end.escape.as_ref());
        if completion.is_some() && escape.is_none() {
            return Err(error(
                source,
                "return requires compositional loop verification",
            ));
        }
        let goal = escape
            .map_or(post, |e| &e.return_post)
            .clone()
            .app(value.clone());
        let key = if path == "loop.exit." {
            "loop.exit".into()
        } else {
            format!("{path}return")
        };
        let proof = self.obligation(proofs, &key, source, context, goal)?;
        if let Some(escape) = escape {
            for (a, b) in &escape.wrappers {
                value = outcome(false, a.clone(), b.clone(), value);
            }
        }
        Ok((value, proof))
    }
}

impl Lowerer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn compose(
        &mut self,
        commands: &[&Command<'_>],
        mut state: State,
        result: Scalar,
        post: &E,
        context: &[(String, E)],
        path: &str,
        proofs: &mut Proofs<'_>,
        completion: Option<&Completion<'_>>,
    ) -> Result<(E, E), Diagnostic> {
        state.allow_contracts = false;
        let Some((command, rest)) = commands.split_first() else {
            if let Some(end) = completion {
                let value = state_tuple::pack(end.names, &state).ann(end.ty.clone());
                let proof = if let Some(join) = &end.join {
                    if join.trivial {
                        E::name("deppy.data.MkUnit")
                    } else {
                        self.compose(
                            &join.rest,
                            state.clone(),
                            result,
                            &join.post,
                            context,
                            path,
                            proofs,
                            join.parent,
                        )?
                        .1
                    }
                } else if let Some(goals) = &end.split {
                    let first = self.obligation(
                        proofs,
                        &format!("{path}preserve"),
                        goals[0].1,
                        context,
                        goals[0].0.clone().app(value.clone()),
                    )?;
                    let second = self.obligation(
                        proofs,
                        &format!("{path}decrease"),
                        goals[1].1,
                        context,
                        goals[1].0.clone().app(value.clone()),
                    )?;
                    E::pair(first, second)
                } else {
                    self.obligation(
                        proofs,
                        path.trim_end_matches('.'),
                        end.source,
                        context,
                        post.clone().app(value.clone()),
                    )?
                };
                let value = if let Some(escape) = &end.escape {
                    outcome(true, end.ty.clone(), escape.output.clone(), value)
                } else {
                    value
                };
                return Ok((value, proof));
            }
            return Err(Diagnostic {
                details: Default::default(),
                span: crate::Span { start: 0, end: 0 },
                message: "every verified path must return a value".into(),
            });
        };
        if let Some(end) = completion.filter(|end| end.join.is_none()) {
            let check = |name: &str, source: &Expr| {
                if !name.starts_with("$expr") && !end.names.iter().any(|n| n == name) {
                    Err(error(
                        source,
                        "every loop assignment must target a declared state variable",
                    ))
                } else {
                    Ok(())
                }
            };
            match command {
                Command::Assign(name, _, source) => check(name, source)?,
                Command::Parallel(bindings) => {
                    for (name, source) in bindings {
                        check(name, source)?;
                    }
                }
                Command::While(inner) => {
                    for name in &inner.names {
                        check(name, inner.test)?;
                    }
                }
                _ => {}
            }
        }
        // A direct verified call is a modular proof boundary. Expression
        // normalization has already named nested calls in evaluation order.
        let candidate = match command {
            Command::Assign(name, annotation, expr) => Some((Some((*name, *annotation)), *expr)),
            Command::Return(expr) => Some((None, *expr)),
            _ => None,
        };
        if let Some((target, Expr::Call(call))) = candidate {
            if let Expr::Name(callee) = call.func.as_ref() {
                if let Some(binding) = self
                    .globals
                    .get(callee.id.as_str())
                    .filter(|b| b.verified)
                    .cloned()
                {
                    if state.scope.locals.contains(callee.id.as_str())
                        || state.scope.assigned.contains(callee.id.as_str())
                    {
                        return Err(error(call, "verified local values are not callable"));
                    }
                    let contract = binding
                        .contract
                        .as_ref()
                        .expect("verified binding carries its contract");
                    if !call.arguments.keywords.is_empty()
                        || call.arguments.args.len() != contract.parameters.len()
                    {
                        return Err(error(
                            call,
                            "verified contract call requires the declared positional arguments",
                        ));
                    }
                    let expected = target
                        .map(|(name, annotation)| state.types.get(name).copied().or(annotation))
                        .unwrap_or(Some(result));
                    if expected.is_some_and(|ty| ty != contract.result)
                        || target.is_some_and(|(name, annotation)| {
                            annotation.is_some()
                                && state
                                    .types
                                    .get(name)
                                    .is_some_and(|old| Some(*old) != annotation)
                        })
                    {
                        return Err(error(call, "verified scalar type mismatch"));
                    }
                    let mut actual = E::name(&binding.name);
                    let mut evidence = E::name(specification_name(&binding.name));
                    let mut pre = contract.pre.clone();
                    let mut post_call = contract.post.clone();
                    for (argument, ty) in call.arguments.args.iter().zip(&contract.parameters) {
                        let value = self.value(argument, &state, Some(*ty))?.0;
                        actual = actual.app(value.clone());
                        evidence = evidence.app(value.clone());
                        pre = pre.app(value.clone());
                        post_call = post_call.app(value);
                    }
                    let key = proofs.call_key(path, target.map(|(n, _)| n).unwrap_or("return"));
                    let source = candidate.unwrap().1;
                    let pre_proof = self.obligation(proofs, &key, source, context, pre.clone())?;
                    let id = self.wildcard;
                    self.wildcard += 1;
                    let value_name = format!("$call_result{id}");
                    let fact_name = format!("$call_spec{id}");
                    let pre_name = format!("$call_pre{id}");
                    let value = E::name(&value_name);
                    let fact_type = post_call.app(value.clone());
                    let mut next_context = context.to_vec();
                    next_context.push((value_name.clone(), contract.result.expr()));
                    next_context.push((fact_name.clone(), fact_type.clone()));
                    let (tail, tail_proof) = if let Some((name, _)) = target {
                        state.scope.locals.insert(name.into());
                        state.scope.aliases.insert(name.into(), value_name.clone());
                        state.types.insert(name.into(), contract.result);
                        let facts = self.local_evidence(
                            &[(name, source)],
                            &state,
                            &mut next_context,
                            path,
                            proofs,
                        )?;
                        let (tail, proof) = self.compose(
                            rest,
                            state,
                            result,
                            post,
                            &next_context,
                            path,
                            proofs,
                            completion,
                        )?;
                        (tail, state_tuple::lets(&facts, proof))
                    } else {
                        self.return_evidence(
                            value,
                            source,
                            post,
                            &next_context,
                            path,
                            proofs,
                            completion,
                        )?
                    };
                    let conclusion = post.clone().app(tail.clone());
                    let denotation = E::let_in(
                        &value_name,
                        Some(contract.result.expr()),
                        actual.clone(),
                        tail,
                    );
                    let continuation = E::lam(
                        &value_name,
                        Plicity::Explicit,
                        Some(contract.result.expr()),
                        E::lam(
                            &fact_name,
                            Plicity::Explicit,
                            Some(fact_type.clone()),
                            tail_proof,
                        ),
                    );
                    // Annotate before application: lambdas need an expected type.
                    let continuation_ty = E::pi(
                        &value_name,
                        Plicity::Explicit,
                        contract.result.expr(),
                        E::pi(&fact_name, Plicity::Explicit, fact_type, conclusion),
                    );
                    let proof = E::let_in(
                        &pre_name,
                        Some(pre),
                        pre_proof,
                        continuation
                            .ann(continuation_ty)
                            .app(actual)
                            .app(evidence.app(E::name(&pre_name))),
                    );
                    return Ok((denotation, proof));
                }
            }
        }
        match command {
            Command::Break(source) => {
                let Some(end) = completion else {
                    return Err(error(*source, "break requires an enclosing loop"));
                };
                let Some(escape) = &end.escape else {
                    return Err(error(
                        *source,
                        "break requires compositional loop verification",
                    ));
                };
                let (value, proof) = self.compose(
                    &escape.rest,
                    state,
                    result,
                    &escape.post,
                    context,
                    &format!("{path}break."),
                    proofs,
                    escape.parent,
                )?;
                Ok((
                    outcome(false, end.ty.clone(), escape.output.clone(), value),
                    proof,
                ))
            }
            Command::Continue(source) => {
                if completion.is_none() {
                    return Err(error(*source, "continue requires an enclosing loop"));
                }
                self.compose(&[], state, result, post, context, path, proofs, completion)
            }
            Command::Assert(source) => {
                let value = self.value(source, &state, Some(Scalar::Bool))?.0;
                let goal = E::eq(Scalar::Bool.expr(), value, E::name("deppy.data.True_"));
                let key = proofs.assertion_key(path, source);
                let evidence = self.obligation(proofs, &key, source, context, goal.clone())?;
                let name = format!("$assert{}", self.wildcard);
                self.wildcard += 1;
                let mut context = context.to_vec();
                context.push((name.clone(), goal.clone()));
                let (value, proof) = self.compose(
                    rest, state, result, post, &context, path, proofs, completion,
                )?;
                Ok((value, E::let_in(name, Some(goal), evidence, proof)))
            }
            Command::Refine(name, scalar, predicate) => {
                self.local_condition(name, *scalar, predicate, &mut state)?;
                self.compose(rest, state, result, post, context, path, proofs, completion)
            }
            Command::Return(expr) => {
                let value = self.value(expr, &state, Some(result))?.0;
                self.return_evidence(value, expr, post, context, path, proofs, completion)
            }
            Command::Assign(name, annotation, expr) => {
                let binding = self.loop_assign(name, *annotation, expr, &mut state)?;
                let mut context = context.to_vec();
                let facts =
                    self.local_evidence(&[(name, expr)], &state, &mut context, path, proofs)?;
                let (value, proof) = self.compose(
                    rest, state, result, post, &context, path, proofs, completion,
                )?;
                let proof = state_tuple::lets(&facts, proof);
                let (name, ty, rhs) = binding;
                Ok((
                    E::let_in(&name, Some(ty.clone()), rhs.clone(), value),
                    E::let_in(name, Some(ty), rhs, proof),
                ))
            }
            Command::Parallel(bindings) => {
                let lowered = self.parallel_values(bindings, &mut state)?;
                let mut context = context.to_vec();
                let facts = self.local_evidence(bindings, &state, &mut context, path, proofs)?;
                let (mut value, proof) = self.compose(
                    rest, state, result, post, &context, path, proofs, completion,
                )?;
                let mut proof = state_tuple::lets(&facts, proof);
                let bindings = lowered;
                for (name, ty, rhs) in bindings.into_iter().rev() {
                    value = E::let_in(&name, Some(ty.clone()), rhs.clone(), value);
                    proof = E::let_in(name, Some(ty), rhs, proof);
                }
                Ok((value, proof))
            }
            Command::If(test, yes, no) => {
                if !rest.is_empty() {
                    if let Some(joined) = self.shared_branch(
                        test,
                        yes,
                        no,
                        rest,
                        state.clone(),
                        result,
                        post,
                        context,
                        path,
                        proofs,
                        completion,
                    )? {
                        return Ok(joined);
                    }
                }
                let guard = self.value(test, &state, Some(Scalar::Bool))?.0;
                let id = self.wildcard;
                self.wildcard += 1;
                let branch_name = format!("$branch{id}");
                let mut branch =
                    |commands: &[Command<'_>], truth: bool| -> Result<(E, E), Diagnostic> {
                        let mut context = context.to_vec();
                        let eq = E::eq(
                            Scalar::Bool.expr(),
                            guard.clone(),
                            E::name(if truth {
                                "deppy.data.True_"
                            } else {
                                "deppy.data.False_"
                            }),
                        );
                        context.push((branch_name.clone(), eq.clone()));
                        let commands = commands
                            .iter()
                            .chain(rest.iter().copied())
                            .collect::<Vec<_>>();
                        let (value, proof) = self.compose(
                            &commands,
                            state.clone(),
                            result,
                            post,
                            &context,
                            &format!("{path}{}.", if truth { "then" } else { "else" }),
                            proofs,
                            completion,
                        )?;
                        Ok((
                            value,
                            E::lam(&branch_name, Plicity::Explicit, Some(eq), proof),
                        ))
                    };
                let (no, no_proof) = branch(no, false)?;
                let (yes, yes_proof) = branch(yes, true)?;
                let value = E::name("deppy.verified.select")
                    .implicit(completion.map_or_else(|| result.expr(), |end| end.output_type()))
                    .app(guard.clone())
                    .app(no.clone())
                    .app(yes.clone());
                let proof = E::name("deppy.verified.select_post_eq")
                    .implicit(completion.map_or_else(|| result.expr(), |end| end.output_type()))
                    .implicit(post.clone())
                    .app(guard)
                    .app(no)
                    .app(yes)
                    .app(no_proof)
                    .app(yes_proof);
                Ok((value, proof))
            }
            Command::While(loop_) => self.compose_loop(
                loop_, rest, state, result, post, context, path, proofs, completion,
            ),
        }
    }
}
