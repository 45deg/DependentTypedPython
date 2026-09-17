use super::*;
impl Lowerer {
    /// Initial nested fragment: split the sole generalized Fin (S k) argument,
    /// with a result independent of that argument. Fin's predecessor is recovered
    /// by a type-level Nat motive, not asserted equal to the outer bound.
    pub(super) fn branch_body(
        &mut self,
        f: &Function,
        body: &Body,
        env: &Env,
        recursion: Option<&Recursion>,
        suffix: &[Parameter],
    ) -> Result<E, Error> {
        self.tick()?;
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
        let E::Fin { bound } = &suffix[0].ty else {
            return Err(Error::UnsupportedMatch(
                "nested match requires Fin (S k)".into(),
            ));
        };
        let E::Succ(k) = bound.as_ref() else {
            return Err(Error::UnsupportedMatch(
                "nested match requires a successor bound".into(),
            ));
        };
        let (zero, step) = coverage(&Kind::Fin { index: 0 }, arms)?;
        let mut result_env = env.clone();
        result_env.remove(scrutinee);
        // A dependent result would need a more general motive; reject it rather
        // than retaining the original index in a supposedly refined branch.
        let result = self
            .rewrite(&f.result, &result_env, None)
            .map_err(|error| {
                if matches!(&error,Error::UnknownName(name) if name==scrutinee) {
                    Error::UnsupportedMatch(
                        "nested Fin result must not depend on the matched index value".into(),
                    )
                } else {
                    error
                }
            })?;
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
        let Body::Return(zero) = &zero.body else {
            return Err(Error::UnsupportedMatch(
                "only one nested Fin split is supported".into(),
            ));
        };
        let Body::Return(step) = &step.body else {
            return Err(Error::UnsupportedMatch(
                "only one nested Fin split is supported".into(),
            ));
        };
        let zero = self.rewrite(zero, &zero_env, recursion)?;
        let step = self.rewrite(step, &step_env, recursion)?;
        Ok(crate::prelude::fin_case(f.motive_level)
            .implicit(result)
            .app(*k.clone())
            .app(E::name(&suffix[0].name))
            .app(zero)
            .app(E::lam(j, Plicity::Explicit, Some(E::fin(*k.clone())), step)))
    }
}
