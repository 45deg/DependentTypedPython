use super::*;
impl Lowerer {
    /// Split the sole generalized Fin (S k) argument with a dependent result.
    /// A type-level Nat motive recovers the predecessor without index coercions.
    pub(super) fn branch_body(
        &mut self,
        f: &Function,
        body: &Body,
        env: &Env,
        recursion: Option<&Recursion>,
        context: (&[Parameter], &[Local]),
    ) -> Result<E, Error> {
        self.tick()?;
        let (suffix, locals) = context;
        if let Body::Let {
            name,
            ty,
            value,
            body,
        } = body
        {
            let local = Local {
                name: name.clone(),
                ty: ty.clone(),
                value: value.clone(),
            };
            let mut env = env.clone();
            let checked = self.local(&local, &mut env, recursion)?;
            let mut locals = locals.to_vec();
            locals.push(local);
            let body = self.branch_body(f, body, &env, recursion, (suffix, &locals))?;
            return Ok(wrap_locals(vec![checked], body));
        }
        let Body::Match { scrutinee, arms } = body else {
            let Body::Return(value) = body else {
                unreachable!()
            };
            return self.rewrite(value, env, recursion);
        };
        if suffix.len() != 1 || !matches!(env.get(scrutinee),Some(E::Name(n)) if n==&suffix[0].name)
        {
            return Err(Error::UnsupportedMatch(
                "nested match must inspect the sole generalized parameter".into(),
            ));
        }
        let E::Fin { bound } = suffix[0].ty.unlocated() else {
            return Err(Error::UnsupportedMatch(
                "nested match requires Fin (S k)".into(),
            ));
        };
        let E::Succ(k) = bound.unlocated() else {
            return Err(Error::UnsupportedMatch(
                "nested match requires a successor bound".into(),
            ));
        };
        let (zero, step) = coverage(&Kind::Fin { index: 0 }, arms)?;
        let mut result_env = env.clone();
        self.clear_locals(locals, &mut result_env);
        result_env.remove(scrutinee);
        // Retain the smaller case combinator for index-independent results.
        let constant_result = match self.rewrite(&f.result, &result_env, None) {
            Ok(result) => Some(result),
            Err(error) if matches!(error.cause(), Error::UnknownName(name) if name == scrutinee) => {
                None
            }
            Err(error) => return Err(error),
        };
        let index = self.fresh();
        result_env.insert(scrutinee.clone(), E::name(&index));
        let result = self.rewrite(&f.result, &result_env, None)?;
        let family = E::lam(
            index,
            Plicity::Explicit,
            Some(E::fin(bound.as_ref().clone())),
            result,
        );
        let Pattern::FZ(zero_bound) = &zero.pattern else {
            unreachable!()
        };
        let Pattern::FS {
            bound: step_bound,
            pred,
        } = &step.pattern
        else {
            unreachable!()
        };
        for names in [vec![zero_bound], vec![step_bound, pred]] {
            let mut seen = HashSet::new();
            for name in names {
                Self::name(name)?;
                if env.contains_key(name) || !seen.insert(name) {
                    return Err(Error::InvalidPattern(
                        "nested pattern shadows an existing binding or repeats a name".into(),
                    ));
                }
            }
        }
        let mut zero_env = env.clone();
        zero_env.insert(zero_bound.clone(), *k.clone());
        zero_env.insert(scrutinee.clone(), E::fz(*k.clone()));
        let mut step_env = env.clone();
        step_env.insert(step_bound.clone(), *k.clone());
        let j = self.bind(&mut step_env, pred)?;
        step_env.insert(scrutinee.clone(), E::fs(*k.clone(), E::name(&j)));
        let zero_locals = self.replay_locals(locals, &mut zero_env, recursion)?;
        let step_locals = self.replay_locals(locals, &mut step_env, recursion)?;
        let zero = wrap_locals(
            zero_locals,
            self.terminal_body(&zero.body, &zero_env, recursion)?,
        );
        let step = wrap_locals(
            step_locals,
            self.terminal_body(&step.body, &step_env, recursion)?,
        );
        let case = if let Some(result) = constant_result {
            crate::prelude::fin_case(f.motive_level)
                .implicit(result)
                .app(*k.clone())
        } else {
            crate::prelude::fin_case_dependent(f.motive_level)
                .app(*k.clone())
                .app(family)
        };
        Ok(case.app(E::name(&suffix[0].name)).app(zero).app(E::lam(
            j,
            Plicity::Explicit,
            Some(E::fin(*k.clone())),
            step,
        )))
    }
    fn terminal_body(
        &mut self,
        body: &Body,
        env: &Env,
        recursion: Option<&Recursion>,
    ) -> Result<E, Error> {
        self.tick()?;
        match body {
            Body::Return(value) => self.rewrite(value, env, recursion),
            Body::Let {
                name,
                ty,
                value,
                body,
            } => {
                let local = Local {
                    name: name.clone(),
                    ty: ty.clone(),
                    value: value.clone(),
                };
                let mut env = env.clone();
                let checked = self.local(&local, &mut env, recursion)?;
                Ok(wrap_locals(
                    vec![checked],
                    self.terminal_body(body, &env, recursion)?,
                ))
            }
            Body::Match { .. } => Err(Error::UnsupportedMatch(
                "only one nested Fin split is supported".into(),
            )),
        }
    }
}
