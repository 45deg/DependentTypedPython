//! Compositional loop boundaries. The body is checked once against a paired
//! preservation/decrease postcondition. The exit continuation is checked for an
//! arbitrary state satisfying the invariant and the false-guard evidence.
use super::*;

pub(super) fn number_loops(commands: &mut [Command<'_>], next: &mut usize) {
    for command in commands {
        match command {
            Command::While(loop_) => {
                *next += 1;
                loop_.id = *next;
                number_loops(&mut loop_.body, next);
            }
            Command::If(_, yes, no) => {
                number_loops(yes, next);
                number_loops(no, next);
            }
            _ => {}
        }
    }
}

fn contains_continue(commands: &[Command<'_>]) -> bool {
    commands.iter().any(|c| match c {
        Command::Continue(_) | Command::Break(_) => true,
        Command::If(_, yes, no) => contains_continue(yes) || contains_continue(no),
        Command::While(loop_) => contains_continue(&loop_.body) || has_exit(&loop_.body),
        _ => false,
    })
}

pub(super) fn has_return(commands: &[Command<'_>]) -> bool {
    commands.iter().any(|c| match c {
        Command::Return(_) => true,
        Command::If(_, a, b) => has_return(a) || has_return(b),
        Command::While(inner) => has_return(&inner.body),
        _ => false,
    })
}
fn has_exit(commands: &[Command<'_>]) -> bool {
    commands.iter().any(|c| match c {
        Command::Break(_) | Command::Return(_) => true,
        Command::If(_, yes, no) => has_exit(yes) || has_exit(no),
        Command::While(inner) => has_return(&inner.body),
        _ => false,
    })
}

// Preserve the existing single-loop certificate API and named proof contexts.
pub(super) fn needs_composition(commands: &[Command<'_>]) -> bool {
    if contains_continue(commands) {
        return true;
    }
    let mut seen_loop = false;
    for command in commands {
        match command {
            Command::While(loop_) => {
                if seen_loop || loops::contains_loop(&loop_.body) {
                    return true;
                }
                seen_loop = true;
            }
            Command::If(_, yes, no)
                if !seen_loop || loops::contains_loop(yes) || loops::contains_loop(no) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}
fn lambda(name: &str, ty: E, body: E) -> E {
    E::lam(name, Plicity::Explicit, Some(ty), body)
}
fn abstract_context(context: &[(String, E)], mut term: E, pi: bool) -> E {
    for (name, ty) in context.iter().rev() {
        term = if pi {
            E::pi(name, Plicity::Explicit, ty.clone(), term)
        } else {
            lambda(name, ty.clone(), term)
        };
    }
    term
}

impl Lowerer {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn compose_loop(
        &mut self,
        loop_: &loops::Loop<'_>,
        rest: &[&Command<'_>],
        state: State,
        result: Scalar,
        post: &E,
        context: &[(String, E)],
        path: &str,
        proofs: &mut contracts::Proofs<'_>,
        completion: Option<&contracts::Completion<'_>>,
    ) -> Result<(E, E), Diagnostic> {
        self.tick(loop_.test.range())?;
        let path = format!("{path}loop.{}.", loop_.id);
        for name in &loop_.names {
            if !state.types.contains_key(name) {
                return Err(error(
                    loop_.test,
                    format!("loop state {name} must be initialized before while"),
                ));
            }
        }
        let id = self.wildcard;
        self.wildcard += 1;
        let state_name = format!("$loop_state{id}");
        let inv_name = format!("$loop_inv{id}");
        let test_name = format!("$loop_test{id}");
        let ty = state_tuple::state_type(&loop_.names, &state);
        let initial = state_tuple::pack(&loop_.names, &state).ann(ty.clone());
        let current = E::name(&state_name);
        let mut symbolic = state.clone();
        let mut fields = vec![];
        let mut tail = current.clone();
        for (i, name) in loop_.names.iter().enumerate() {
            let fresh = format!("$loop_field{id}_{i}");
            fields.push((fresh.clone(), state.types[name].expr(), tail.clone().fst()));
            symbolic.scope.aliases.insert(name.clone(), fresh);
            tail = tail.snd();
        }
        let close = |body| lambda(&state_name, ty.clone(), state_tuple::lets(&fields, body));
        let guard = close(self.value(loop_.test, &symbolic, Some(Scalar::Bool))?.0);
        let mut inv_ty = E::Universe(0);
        let mut measure_ty = E::Nat;
        let annotation_names = loop_.annotation_names.as_ref().unwrap_or(&loop_.names);
        for name in annotation_names.iter().rev() {
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
            for name in annotation_names {
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
        // Share the semantic functions in both the implementation and its proof.
        let mut bindings = vec![];
        let mut share = |suffix: &str, domain: E, value: E| {
            let name = format!("$loop_{suffix}{id}");
            bindings.push((
                name.clone(),
                E::pi("$s", Plicity::Explicit, ty.clone(), domain),
                value,
            ));
            E::name(name)
        };
        let guard = share("guard", Scalar::Bool.expr(), guard);
        let inv = share("invariant", E::Universe(0), close(inv));
        let measure = share("measure", E::Nat, close(measure));
        let init = self.obligation(
            proofs,
            &format!("{path}init"),
            loop_.invariant.unwrap_or(loop_.test),
            context,
            inv.clone().app(initial.clone()),
        )?;
        let locals = |truth| {
            vec![
                (state_name.clone(), ty.clone()),
                (inv_name.clone(), inv.clone().app(current.clone())),
                (
                    test_name.clone(),
                    E::eq(
                        Scalar::Bool.expr(),
                        guard.clone().app(current.clone()),
                        E::name(if truth {
                            "deppy.data.True_"
                        } else {
                            "deppy.data.False_"
                        }),
                    ),
                ),
            ]
        };
        let body_locals = locals(true);
        let mut body_context = context.to_vec();
        body_context.extend(body_locals.clone());
        let entries = loop_
            .names
            .iter()
            .map(|n| (n.as_str(), loop_.invariant.unwrap_or(loop_.test)))
            .collect::<Vec<_>>();
        let facts = self.local_evidence(
            &entries,
            &symbolic,
            &mut body_context,
            &format!("{path}step.entry."),
            proofs,
        )?;
        let decrease = lambda(
            "$next",
            ty.clone(),
            E::name("deppy.nat_order.LT")
                .app(measure.clone().app(E::name("$next")))
                .app(measure.clone().app(current.clone())),
        );
        let next_post = lambda(
            "$next",
            ty.clone(),
            E::sigma(
                "$preserved",
                inv.clone().app(E::name("$next")),
                decrease.clone().app(E::name("$next")),
            ),
        );
        let escaping = has_exit(&loop_.body);
        let output = completion.map_or_else(|| result.expr(), |end| end.output_type());
        let outcome_ty = contracts::sum_type(ty.clone(), output.clone());
        let step_post = if escaping {
            lambda(
                "$outcome",
                outcome_ty.clone(),
                E::name("deppy.verified_loop.outcome_post")
                    .implicit(ty.clone())
                    .implicit(output.clone())
                    .app(next_post.clone())
                    .app(post.clone())
                    .app(E::name("$outcome")),
            )
        } else {
            next_post
        };
        let escape = if escaping {
            let parent_escape = completion.and_then(|e| e.escape.as_ref());
            let mut wrappers = parent_escape.map_or_else(Vec::new, |e| e.wrappers.clone());
            wrappers.push((ty.clone(), output.clone()));
            Some(contracts::Escape {
                rest: rest.to_vec(),
                parent: completion,
                post: post.clone(),
                output: output.clone(),
                return_post: parent_escape.map_or_else(|| post.clone(), |e| e.return_post.clone()),
                wrappers,
            })
        } else {
            None
        };
        let end = contracts::Completion {
            names: &loop_.names,
            ty: ty.clone(),
            source: loop_.test,
            escape,
            join: None,
            split: Some([
                (inv.clone(), loop_.invariant.unwrap_or(loop_.test)),
                (decrease, loop_.measure),
            ]),
        };
        let (next, step_proof) = self.compose(
            &loop_.body.iter().collect::<Vec<_>>(),
            symbolic.clone(),
            result,
            &step_post,
            &body_context,
            &format!("{path}step."),
            proofs,
            Some(&end),
        )?;
        let step = share(
            "step",
            if escaping { outcome_ty } else { ty.clone() },
            close(next.clone()),
        );
        let combined_ty = abstract_context(
            &body_locals,
            state_tuple::lets(&fields, step_post.app(next)),
            true,
        );
        let combined = abstract_context(
            &body_locals,
            state_tuple::lets(&fields, state_tuple::lets(&facts, step_proof)),
            false,
        );
        let combined_name = format!("$loop_step_proof{id}");
        let evidence = E::name(&combined_name)
            .app(current.clone())
            .app(E::name(&inv_name))
            .app(E::name(&test_name));
        let preserve = abstract_context(&body_locals, evidence.clone().fst(), false);
        let decrease = abstract_context(&body_locals, evidence.snd(), false);
        let exit_locals = locals(false);
        let mut exit_context = context.to_vec();
        exit_context.extend(exit_locals.clone());
        let facts = self.local_evidence(
            &entries,
            &symbolic,
            &mut exit_context,
            &format!("{path}exit.entry."),
            proofs,
        )?;
        let (after, exit_proof) = self.compose(
            rest,
            symbolic,
            result,
            post,
            &exit_context,
            &format!("{path}exit."),
            proofs,
            completion,
        )?;
        let finish = share(
            "finish",
            completion.map_or_else(|| result.expr(), |end| end.output_type()),
            close(after),
        );
        let final_post = lambda(
            &state_name,
            ty.clone(),
            post.clone().app(finish.clone().app(current)),
        );
        let exit_proof = abstract_context(
            &exit_locals,
            state_tuple::lets(&fields, state_tuple::lets(&facts, exit_proof)),
            false,
        );
        let (value, correct) = if escaping {
            let fuel = measure.clone().app(initial.clone());
            let value = E::name("deppy.verified_loop.run")
                .implicit(ty.clone())
                .implicit(output.clone())
                .app(guard.clone())
                .app(step.clone())
                .app(finish.clone())
                .app(fuel.clone())
                .app(initial.clone());
            let correct = E::name("deppy.verified_loop.run_correct")
                .implicit(ty)
                .implicit(output)
                .implicit(inv)
                .implicit(post.clone())
                .app(guard)
                .app(step)
                .app(finish)
                .app(measure)
                .app(E::name(&combined_name))
                .app(exit_proof)
                .app(fuel.clone())
                .app(initial)
                .app(init)
                .app(E::name("deppy.nat_order.le_refl").app(fuel));
            (value, correct)
        } else {
            let end = E::name("deppy.verified_loop.iterate")
                .implicit(ty.clone())
                .app(guard.clone())
                .app(step.clone())
                .app(measure.clone().app(initial.clone()))
                .app(initial.clone());
            let value = finish.app(end);
            let mut correct = E::name("deppy.verified_loop.loop_correct");
            for arg in [ty, guard, step, measure, inv, final_post, initial] {
                correct = correct.implicit(arg);
            }
            (
                value,
                correct.app(E::pair(
                    init,
                    E::pair(preserve, E::pair(decrease, exit_proof)),
                )),
            )
        };
        let proof = E::let_in(combined_name, Some(combined_ty), combined, correct);
        let location = deppy_elab::SourceLocation {
            source: self.namespace.clone(),
            start: loop_.test.range().start().to_usize(),
            end: loop_.test.range().end().to_usize(),
        };
        Ok((
            state_tuple::lets(&bindings, value).located(location.clone()),
            state_tuple::lets(&bindings, proof).located(location),
        ))
    }
}
