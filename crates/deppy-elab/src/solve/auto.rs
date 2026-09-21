//! Small, bounded, proof-producing search. Hints are supplied by the frontend;
//! this module knows no Python names or arithmetic axioms.
use super::*;

impl State {
    // Failed alternatives must not leak unification assignments or fresh ids.
    // Work already spent is deliberately not refunded to the elaboration budget.
    fn proof_attempt(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, Error>,
    ) -> Result<Option<T>, Error> {
        let metas = self.metas.clone();
        let next_id = self.next_id;
        match f(self) {
            Ok(term) => Ok(Some(term)),
            Err(error) => {
                self.metas = metas;
                self.next_id = next_id;
                match error {
                    Error::CannotUnify
                    | Error::OccursCheck
                    | Error::ScopeEscape
                    | Error::NonPattern
                    | Error::UnsolvedMeta { .. } => Ok(None),
                    other => Err(other),
                }
            }
        }
    }

    fn proof_facts(
        &mut self,
        value: T,
        ty: T,
        depth: usize,
        facts: &mut Vec<(T, T)>,
    ) -> Result<(), Error> {
        facts.push((value.clone(), ty.clone()));
        if depth > 0 {
            if let Term::Sigma { id, domain, body } = self.whnf(&ty)?.as_ref() {
                let first = Term::Fst(value.clone()).arc();
                let second_ty = self.replace(body, *id, first.clone())?;
                self.proof_facts(first, domain.clone(), depth - 1, facts)?;
                self.proof_facts(Term::Snd(value).arc(), second_ty, depth - 1, facts)?;
            }
        }
        Ok(())
    }

    pub(super) fn auto_proof(
        &mut self,
        ctx: &Context,
        expected: &T,
        hints: &[String],
    ) -> Result<Option<T>, Error> {
        let mut facts = vec![];
        for local in ctx.iter().rev() {
            let value = local
                .value
                .clone()
                .unwrap_or_else(|| Term::Local(local.id).arc());
            self.proof_facts(value, local.ty.clone(), 8, &mut facts)?;
        }
        let mut rules = vec![];
        for hint in hints {
            if self.globals.contains_key(hint) {
                rules.push(self.synth(ctx, &Expr::name(hint))?);
            }
        }
        let mut attempts = 256;
        let start = self.metas.len();
        // Prefer existing evidence. Lemma premises use facts/reflexivity only;
        // the depth bound permits conjunctions, not recursive lemma chaining.
        for depth in [0, 8] {
            let result = self.proof_attempt(|s| {
                let proof = s.search_proof(ctx, expected, &facts, &rules, depth, &mut attempts)?;
                let proof = s.expand(&proof)?;
                // Keep complete applications for kernel rechecking, but discard
                // search-only metas and their duplicate context telescopes.
                for index in 0..start {
                    if let Some(solution) = s.metas[index].solution.clone() {
                        s.metas[index].solution = Some(s.expand(&solution)?);
                    }
                }
                Ok(proof)
            })?;
            if result.is_some() {
                self.metas.truncate(start);
                return Ok(result);
            }
        }
        Ok(None)
    }

    fn search_proof(
        &mut self,
        ctx: &Context,
        expected: &T,
        facts: &[(T, T)],
        rules: &[(T, T)],
        depth: usize,
        attempts: &mut usize,
    ) -> Result<T, Error> {
        self.tick()?;
        if *attempts == 0 {
            return Err(Error::CannotUnify);
        }
        *attempts -= 1;
        for (proof, ty) in facts {
            if let Some(proof) = self.proof_attempt(|s| {
                s.unify(ty, expected)?;
                Ok(proof.clone())
            })? {
                return Ok(proof);
            }
        }
        let target = self.whnf(expected)?;
        if let Term::Eq { ty, left, right } = target.as_ref() {
            if let Some(proof) = self.proof_attempt(|s| {
                s.unify(left, right)?;
                Ok(Term::Refl {
                    ty: ty.clone(),
                    value: left.clone(),
                }
                .arc())
            })? {
                return Ok(proof);
            }
        }
        if depth == 0 {
            return Err(Error::CannotUnify);
        }
        if let Term::Sigma { id, domain, body } = target.as_ref() {
            if let Some(proof) = self.proof_attempt(|s| {
                let fst = s.search_proof(ctx, domain, facts, rules, depth - 1, attempts)?;
                let second = s.replace(body, *id, fst.clone())?;
                let snd = s.search_proof(ctx, &second, facts, rules, depth - 1, attempts)?;
                Ok(Term::Pair {
                    ty: expected.clone(),
                    fst,
                    snd,
                }
                .arc())
            })? {
                return Ok(proof);
            }
        }
        for (rule, rule_ty) in rules {
            if *attempts == 0 {
                break;
            }
            *attempts -= 1;
            if let Some(proof) = self.proof_attempt(|s| {
                let mut proof = rule.clone();
                let mut ty = rule_ty.clone();
                let mut arguments = vec![];
                while let Term::Pi {
                    id, domain, body, ..
                } = s.whnf(&ty)?.as_ref()
                {
                    let argument = s.meta(ctx, domain.clone());
                    arguments.push((argument.clone(), domain.clone()));
                    proof = Term::App(proof, argument.clone()).arc();
                    ty = s.replace(body, *id, argument)?;
                }
                // Infer indices from the conclusion before attempting premises.
                s.unify(&ty, expected)?;
                for (argument, domain) in &arguments {
                    match s.expand(argument) {
                        Ok(_) => continue,
                        Err(Error::UnsolvedMeta { .. }) => {}
                        Err(error) => return Err(error),
                    }
                    // Unconstrained data/type parameters must be inferred from
                    // proof premises, never guessed by proof search.
                    if matches!(s.whnf(domain)?.as_ref(), Term::Nat | Term::Universe(_)) {
                        continue;
                    }
                    let evidence = s.search_proof(ctx, domain, facts, rules, 0, attempts)?;
                    s.unify(argument, &evidence)?;
                }
                s.expand(&proof)
            })? {
                return Ok(proof);
            }
        }
        Err(Error::CannotUnify)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_alternatives_restore_assignments_to_existing_metas() {
        let mut state = State::new(10_000);
        let nat = Term::Nat.arc();
        let zero = Term::Zero.arc();
        let one = Term::Succ(zero.clone()).arc();
        let two = Term::Succ(one.clone()).arc();
        let index = state.meta(&vec![], nat.clone());
        let target = Term::Eq {
            ty: nat.clone(),
            left: index.clone(),
            right: zero.clone(),
        }
        .arc();
        // Matching this candidate assigns index := 1 before 2 = 0 fails.
        let wrong = Term::Eq {
            ty: nat,
            left: one,
            right: two,
        }
        .arc();
        let (context, _) = state.bind(&vec![], "wrong", wrong);
        let proof = state.auto_proof(&context, &target, &[]).unwrap().unwrap();
        assert!(matches!(proof.as_ref(), Term::Refl { .. }));
        assert_eq!(state.expand(&index).unwrap(), zero);
        assert_eq!(state.metas.len(), 1);
    }

    #[test]
    fn exhaustion_is_not_misreported_as_an_unsolved_logical_goal() {
        let mut state = State::new(0);
        let target = Term::Eq {
            ty: Term::Nat.arc(),
            left: Term::Zero.arc(),
            right: Term::Zero.arc(),
        }
        .arc();
        assert!(matches!(
            state.auto_proof(&vec![], &target, &[]),
            Err(Error::BudgetExceeded)
        ));
        assert!(state.metas.is_empty());
    }
}
