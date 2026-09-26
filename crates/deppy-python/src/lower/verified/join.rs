//! Share a normal branch continuation as a typed state-to-result function.
//! Its path-specific proof obligations are still checked with each predecessor's
//! facts. Transfer edges never enter this normal join.
use super::*;
fn unit_post(e: &E) -> bool {
    match e {
        E::Name(n) => n == "deppy.data.Unit",
        E::Lam { body, .. } => unit_post(body),
        E::Ann { term, .. } => unit_post(term),
        E::App { function, .. } => unit_post(function),
        _ => false,
    }
}
fn written(commands: &[Command<'_>], names: &mut HashSet<String>) {
    for c in commands {
        match c {
            Command::Assign(n, _, _) => {
                names.insert((*n).into());
            }
            Command::Parallel(bs) => {
                names.extend(bs.iter().map(|(n, _)| (*n).to_owned()));
            }
            Command::If(_, a, b) => {
                written(a, names);
                written(b, names);
            }
            Command::While(loop_) => names.extend(loop_.names.iter().cloned()),
            _ => {}
        }
    }
}
impl Lowerer {
    fn computational_tail(&self, commands: &[&Command<'_>]) -> bool {
        commands.iter().all(|c| match c {
            Command::Assign(_, _, e) | Command::Return(e) => !self.has_contract_call(e),
            Command::Parallel(bs) => bs.iter().all(|(_, e)| !self.has_contract_call(e)),
            Command::If(e, a, b) => {
                !self.has_contract_call(e)
                    && self.computational_tail(&a.iter().collect::<Vec<_>>())
                    && self.computational_tail(&b.iter().collect::<Vec<_>>())
            }
            _ => false,
        })
    }
    fn join_shape(
        &mut self,
        commands: &[Command<'_>],
        mut state: State,
    ) -> Result<Option<State>, Diagnostic> {
        state.allow_contracts = true;
        for command in commands {
            match command {
                Command::Assign(name, annotation, expr) => {
                    self.loop_assign(name, *annotation, expr, &mut state)?;
                }
                Command::Parallel(bindings) => {
                    self.parallel_values(bindings, &mut state)?;
                }
                Command::Assert(_) => {}
                Command::While(loop_) if !flow::has_return(&loop_.body) => {}
                Command::If(_, yes, no) => {
                    let Some(left) = self.join_shape(yes, state.clone())? else {
                        return Ok(None);
                    };
                    let Some(right) = self.join_shape(no, state.clone())? else {
                        return Ok(None);
                    };
                    state.types = left
                        .types
                        .into_iter()
                        .filter(|(n, ty)| right.types.get(n) == Some(ty))
                        .collect();
                    state.scope.locals.extend(state.types.keys().cloned());
                }
                _ => return Ok(None),
            }
        }
        Ok(Some(state))
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn shared_branch(
        &mut self,
        test: &Expr,
        yes: &[Command<'_>],
        no: &[Command<'_>],
        rest: &[&Command<'_>],
        state: State,
        result: Scalar,
        post: &E,
        context: &[(String, E)],
        path: &str,
        proofs: &mut contracts::Proofs<'_>,
        completion: Option<&contracts::Completion<'_>>,
    ) -> Result<Option<(E, E)>, Diagnostic> {
        let Some(left) = self.join_shape(yes, state.clone())? else {
            return Ok(None);
        };
        let Some(right) = self.join_shape(no, state.clone())? else {
            return Ok(None);
        };
        let mut writes = HashSet::new();
        written(yes, &mut writes);
        written(no, &mut writes);
        let mut names = left
            .types
            .iter()
            .filter(|(n, ty)| writes.contains(*n) && right.types.get(*n) == Some(*ty))
            .map(|(n, _)| n.clone())
            .collect::<Vec<_>>();
        names.sort();
        // Refinement declarations have lexical captures; those remain in the
        // predecessor until a future join representation can carry their scope.
        let mut symbolic = state.clone();
        symbolic
            .types
            .extend(names.iter().map(|n| (n.clone(), left.types[n])));
        symbolic.scope.locals.extend(names.iter().cloned());
        let ty = state_tuple::state_type(&names, &symbolic);
        let id = self.wildcard;
        self.wildcard += 1;
        let parameter = format!("$join_state{id}");
        let function = format!("$join_continuation{id}");
        let mut tail = E::name(&parameter);
        let mut fields = vec![];
        for (i, n) in names.iter().enumerate() {
            let field = format!("$join_field{id}_{i}");
            fields.push((field.clone(), symbolic.types[n].expr(), tail.clone().fst()));
            symbolic.scope.aliases.insert(n.clone(), field);
            tail = tail.snd();
        }
        let output_ty = completion.map_or_else(|| result.expr(), |end| end.output_type());
        // Only the denotation is retained here. All its obligations are checked
        // below in the original predecessor contexts, never assumed from scratch.
        let mut scratch = contracts::Proofs::empty("$join", false);
        scratch.denotation_only = true;
        let (body, _) = self.compose(
            rest,
            symbolic,
            result,
            post,
            context,
            "$join.",
            &mut scratch,
            completion,
        )?;
        let body = E::lam(
            &parameter,
            Plicity::Explicit,
            Some(ty.clone()),
            state_tuple::lets(&fields, body),
        );
        let function_ty = E::pi(&parameter, Plicity::Explicit, ty.clone(), output_ty.clone());
        let join_post = E::lam(
            &parameter,
            Plicity::Explicit,
            Some(ty.clone()),
            post.clone()
                .app(E::name(&function).app(E::name(&parameter))),
        );
        let end = contracts::Completion {
            names: &names,
            ty: ty.clone(),
            source: test,
            split: None,
            escape: None,
            join: Some(contracts::Join {
                trivial: proofs.denotation_only
                    || (proofs.automatic_only()
                        && state.refinements.is_empty()
                        && unit_post(post)
                        && self.computational_tail(rest)),
                rest: rest.to_vec(),
                post: post.clone(),
                parent: completion,
            }),
        };
        let guard = self.value(test, &state, Some(Scalar::Bool))?.0;
        let branch_name = format!("$join_test{id}");
        let mut branch = |commands: &[Command<'_>], truth: bool| -> Result<(E, E), Diagnostic> {
            let eq = E::eq(
                Scalar::Bool.expr(),
                guard.clone(),
                E::name(if truth {
                    "deppy.data.True_"
                } else {
                    "deppy.data.False_"
                }),
            );
            let mut context = context.to_vec();
            context.push((branch_name.clone(), eq.clone()));
            let (value, proof) = self.compose(
                &commands.iter().collect::<Vec<_>>(),
                state.clone(),
                result,
                &join_post,
                &context,
                &format!("{path}{}.", if truth { "then" } else { "else" }),
                proofs,
                Some(&end),
            )?;
            Ok((
                value,
                E::lam(&branch_name, Plicity::Explicit, Some(eq), proof),
            ))
        };
        let (no, no_proof) = branch(no, false)?;
        let (yes, yes_proof) = branch(yes, true)?;
        let selected = E::name("deppy.verified.select")
            .implicit(ty.clone())
            .app(guard.clone())
            .app(no.clone())
            .app(yes.clone());
        let value = E::name(&function).app(selected);
        let proof = E::name("deppy.verified.select_post_eq")
            .implicit(ty)
            .implicit(join_post)
            .app(guard)
            .app(no)
            .app(yes)
            .app(no_proof)
            .app(yes_proof);
        Ok(Some((
            E::let_in(&function, Some(function_ty.clone()), body.clone(), value),
            E::let_in(function, Some(function_ty), body, proof),
        )))
    }
}
