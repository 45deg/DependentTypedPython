//! Modular call proofs. A continuation is checked for every result satisfying
//! the callee's contract, then instantiated using its checked companion theorem.
use super::*;

#[derive(Clone, Debug)]
pub(crate) struct Contract {
    parameters: Vec<Scalar>,
    pub(super) result: Scalar,
    pre: E,
    post: E,
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
}

pub(super) struct Proofs<'a> {
    entries: HashMap<String, &'a Expr>,
    used: HashSet<String>,
    counts: HashMap<String, usize>,
    function: String,
    automatic: bool,
    pub(super) hints: Vec<String>,
}
impl<'a> Proofs<'a> {
    pub(super) fn empty(function: &str, automatic: bool) -> Self {
        Self {
            entries: HashMap::new(),
            used: HashSet::new(),
            counts: HashMap::new(),
            function: function.into(),
            automatic,
            hints: vec![],
        }
    }

    pub(super) fn parse(
        expr: &'a Expr,
        function: &str,
        automatic: bool,
    ) -> Result<Self, Diagnostic> {
        let Expr::Dict(dict) = expr else {
            return Err(error(
                expr,
                "proofs requires a dictionary of named VC proofs",
            ));
        };
        let mut entries = HashMap::new();
        for item in &dict.items {
            let Some(Expr::StringLiteral(key)) = &item.key else {
                return Err(error(expr, "proofs keys must be literal strings"));
            };
            if entries
                .insert(key.value.to_str().to_owned(), &item.value)
                .is_some()
            {
                return Err(error(key, "duplicate VC proof name"));
            }
        }
        Ok(Self {
            entries,
            used: HashSet::new(),
            counts: HashMap::new(),
            function: function.into(),
            automatic,
            hints: vec![],
        })
    }
    pub(super) fn finish(&self) -> Result<(), Diagnostic> {
        if let Some((key, expr)) = self
            .entries
            .iter()
            .filter(|(k, _)| !self.used.contains(*k))
            .min_by_key(|(k, _)| *k)
        {
            return Err(error(*expr, format!("unknown or unused VC proof: {key}")));
        }
        Ok(())
    }
    pub(super) fn call_key(&mut self, path: &str, name: &str) -> String {
        self.assignment_key(path, "call", name, "requires")
    }
    fn assignment_key(&mut self, path: &str, kind: &str, name: &str, suffix: &str) -> String {
        let base = format!("{path}{kind}.{name}");
        let count = self.counts.entry(base.clone()).or_default();
        *count += 1;
        if *count == 1 {
            format!("{base}.{suffix}")
        } else {
            format!("{base}.{}.{suffix}", *count)
        }
    }
}

impl Lowerer {
    pub(super) fn obligation(
        &mut self,
        proofs: &mut Proofs<'_>,
        key: &str,
        source: &Expr,
        context: &[(String, E)],
        goal: E,
    ) -> Result<E, Diagnostic> {
        proofs.used.insert(key.into());
        let proof = if let Some(expr) = proofs.entries.get(key) {
            if let Expr::Lambda(lambda) = expr {
                let parameters = lambda
                    .parameters
                    .as_deref()
                    .ok_or_else(|| error(lambda, "VC proof lambda requires context parameters"))?;
                self.parameters(parameters)?;
                let parameters = parameters
                    .posonlyargs
                    .iter()
                    .chain(&parameters.args)
                    .collect::<Vec<_>>();
                if parameters.len() != context.len() {
                    return Err(error(
                        lambda,
                        format!(
                            "VC {key} proof requires {} context parameters",
                            context.len()
                        ),
                    ));
                }
                // Instantiate the proof callback in the actual symbolic context.
                // Re-abstracting entry variables here would detach their SSA lets
                // from those variables, especially in loop initialization goals.
                let mut scope = Scope::default();
                for (parameter, (name, _)) in parameters.iter().zip(context) {
                    let local = parameter.parameter.name.to_string();
                    scope.locals.insert(local.clone());
                    scope.aliases.insert(local, name.clone());
                }
                self.expr(&lambda.body, &scope)?
            } else {
                let mut proof = self.expr(expr, &Scope::default())?;
                for (name, _) in context {
                    proof = proof.app(E::name(name));
                }
                proof
            }
        } else {
            let name = format!("{}.{}", proofs.function, key);
            let goal = if proofs.automatic {
                E::AutoProof {
                    name,
                    hints: [
                        "deppy.data.MkUnit",
                        "deppy.nat_order.le_refl",
                        "deppy.verified.nat_lt_true",
                        "deppy.verified.nat_le_true",
                        "deppy.verified.nat_lt_false_zero",
                        "deppy.nat_order.pred_lt",
                        "deppy.verified.pred_lt_true",
                        "deppy.verified.lt_le_bound",
                        "deppy.nat_order.le_weaken",
                        "deppy.nat_order.le_trans",
                    ]
                    .into_iter()
                    .map(str::to_owned)
                    .chain(proofs.hints.iter().cloned())
                    .collect(),
                }
            } else {
                E::UserHole(name)
            };
            goal.located(deppy_elab::SourceLocation {
                source: self.namespace.clone(),
                start: source.range().start().to_usize(),
                end: source.range().end().to_usize(),
            })
        };
        Ok(proof.ann(goal))
    }

    pub(super) fn local_condition(
        &mut self,
        name: &str,
        scalar: Scalar,
        predicate: &Expr,
        state: &mut State,
    ) -> Result<(), Diagnostic> {
        if state.refinements.contains_key(name) {
            return Err(error(
                predicate,
                "a local refinement may only be declared once",
            ));
        }
        if state.types.get(name).is_some_and(|old| *old != scalar) {
            return Err(error(
                predicate,
                "verified reassignment cannot change a local's type",
            ));
        }
        let condition = self.expr(predicate, &state.scope)?.ann(E::pi(
            "$value",
            Plicity::Explicit,
            scalar.expr(),
            E::Universe(0),
        ));
        state.refinements.insert(name.into(), condition);
        Ok(())
    }

    pub(super) fn local_evidence(
        &mut self,
        names: &[(&str, &Expr)],
        state: &State,
        context: &mut Vec<(String, E)>,
        path: &str,
        proofs: &mut Proofs<'_>,
    ) -> Result<Vec<(String, E, E)>, Diagnostic> {
        let mut bindings = vec![];
        for (name, source) in names {
            if let Some(predicate) = state.refinements.get(*name) {
                let value_name = state.scope.aliases.get(*name).unwrap();
                if !context.iter().any(|(n, _)| n == value_name) {
                    context.push((value_name.clone(), state.types[*name].expr()));
                }
                let goal = predicate.clone().app(E::name(value_name));
                let key = proofs.assignment_key(path, "local", name, "refined");
                let proof = self.obligation(proofs, &key, source, context, goal.clone())?;
                let fact = format!("$local_fact{}", self.wildcard);
                self.wildcard += 1;
                context.push((fact.clone(), goal.clone()));
                bindings.push((fact, goal, proof));
            }
        }
        Ok(bindings)
    }

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
                let value = loops::pack(end.names, &state).ann(end.ty.clone());
                let proof = self.obligation(
                    proofs,
                    path.trim_end_matches('.'),
                    end.source,
                    context,
                    post.clone().app(value.clone()),
                )?;
                return Ok((value, proof));
            }
            return Err(Diagnostic {
                details: Default::default(),
                span: crate::Span { start: 0, end: 0 },
                message: "every verified path must return a value".into(),
            });
        };
        if let (Some(end), Command::Return(_)) = (completion, command) {
            return Err(error(end.source, "return inside a loop is unsupported"));
        }
        // A direct verified call is a modular proof boundary. Nested calls must
        // be named by an assignment, so evaluation order and goals are explicit.
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
                        (tail, loops::lets(&facts, proof))
                    } else {
                        let proof = self.obligation(
                            proofs,
                            &if path == "loop.exit." {
                                "loop.exit".into()
                            } else {
                                format!("{path}return")
                            },
                            source,
                            &next_context,
                            post.clone().app(value.clone()),
                        )?;
                        (value, proof)
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
            Command::Refine(name, scalar, predicate) => {
                self.local_condition(name, *scalar, predicate, &mut state)?;
                self.compose(rest, state, result, post, context, path, proofs, completion)
            }
            Command::Return(expr) => {
                let value = self.value(expr, &state, Some(result))?.0;
                let proof = self.obligation(
                    proofs,
                    &if path == "loop.exit." {
                        "loop.exit".into()
                    } else {
                        format!("{path}return")
                    },
                    expr,
                    context,
                    post.clone().app(value.clone()),
                )?;
                Ok((value, proof))
            }
            Command::Assign(name, annotation, expr) => {
                let binding = self.loop_assign(name, *annotation, expr, &mut state)?;
                let mut context = context.to_vec();
                let facts =
                    self.local_evidence(&[(name, expr)], &state, &mut context, path, proofs)?;
                let (value, proof) = self.compose(
                    rest, state, result, post, &context, path, proofs, completion,
                )?;
                let proof = loops::lets(&facts, proof);
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
                let mut proof = loops::lets(&facts, proof);
                let bindings = lowered;
                for (name, ty, rhs) in bindings.into_iter().rev() {
                    value = E::let_in(&name, Some(ty.clone()), rhs.clone(), value);
                    proof = E::let_in(name, Some(ty), rhs, proof);
                }
                Ok((value, proof))
            }
            Command::If(test, yes, no) => {
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
                    .implicit(completion.map_or_else(|| result.expr(), |end| end.ty.clone()))
                    .app(guard.clone())
                    .app(no.clone())
                    .app(yes.clone());
                let proof = E::name("deppy.verified.select_post_eq")
                    .implicit(completion.map_or_else(|| result.expr(), |end| end.ty.clone()))
                    .implicit(post.clone())
                    .app(guard)
                    .app(no)
                    .app(yes)
                    .app(no_proof)
                    .app(yes_proof);
                Ok((value, proof))
            }
            Command::While(loop_) => Err(error(
                loop_.test,
                "contract composition inside while is not yet supported",
            )),
        }
    }
}
