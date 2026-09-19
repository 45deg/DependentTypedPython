use super::*;

impl State {
    fn core(&mut self, term: &T, scope: &mut Vec<Id>) -> Result<Tm, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
            Term::Data { op, arguments } => Core::Data {
                op: *op,
                arguments: arguments
                    .iter()
                    .map(|x| self.core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Term::Global(id) => Core::Global(*id),
            Term::Inductive { id, parameters } => Core::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Term::Constructor {
                id,
                parameters,
                fields,
            } => Core::Constructor {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.core(x, scope))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Term::Elim {
                id,
                parameters,
                level,
                motive,
                branch,
                scrutinee,
            } => Core::Elim {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.core(x, scope))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.core(motive, scope)?,
                branch: self.core(branch, scope)?,
                scrutinee: self.core(scrutinee, scope)?,
            },
            Term::Sigma { id, domain, body } => {
                let domain = self.core(domain, scope)?;
                scope.push(*id);
                let codomain = self.core(body, scope)?;
                scope.pop();
                Core::Sigma { domain, codomain }
            }
            Term::Pair { ty, fst, snd } => Core::Pair {
                ty: self.core(ty, scope)?,
                fst: self.core(fst, scope)?,
                snd: self.core(snd, scope)?,
            },
            Term::Fst(p) => Core::Fst(self.core(p, scope)?),
            Term::Snd(p) => Core::Snd(self.core(p, scope)?),
            Term::Local(id) => Core::Var(
                scope
                    .iter()
                    .rev()
                    .position(|x| x == id)
                    .ok_or(Error::ScopeEscape)?,
            ),
            Term::Universe(level) => Core::Universe(*level),
            Term::Nat => Core::Nat,
            Term::Zero => Core::Zero,
            Term::Eq { ty, left, right } => Core::Eq {
                ty: self.core(ty, scope)?,
                left: self.core(left, scope)?,
                right: self.core(right, scope)?,
            },
            Term::Refl { ty, value } => Core::Refl {
                ty: self.core(ty, scope)?,
                value: self.core(value, scope)?,
            },
            Term::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => Core::J {
                level: *level,
                ty: self.core(ty, scope)?,
                left: self.core(left, scope)?,
                motive: self.core(motive, scope)?,
                base: self.core(base, scope)?,
                right: self.core(right, scope)?,
                proof: self.core(proof, scope)?,
            },
            Term::Vec { ty, len } => Core::Vec {
                ty: self.core(ty, scope)?,
                len: self.core(len, scope)?,
            },
            Term::VNil { ty } => Core::VNil {
                ty: self.core(ty, scope)?,
            },
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => Core::VCons {
                ty: self.core(ty, scope)?,
                len: self.core(len, scope)?,
                head: self.core(head, scope)?,
                tail: self.core(tail, scope)?,
            },
            Term::Fin { bound } => Core::Fin {
                bound: self.core(bound, scope)?,
            },
            Term::FZ { bound } => Core::FZ {
                bound: self.core(bound, scope)?,
            },
            Term::FS { bound, pred } => Core::FS {
                bound: self.core(bound, scope)?,
                pred: self.core(pred, scope)?,
            },
            Term::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => Core::VecElim {
                level: *level,
                ty: self.core(ty, scope)?,
                motive: self.core(motive, scope)?,
                nil: self.core(nil, scope)?,
                cons: self.core(cons, scope)?,
                len: self.core(len, scope)?,
                scrutinee: self.core(scrutinee, scope)?,
            },
            Term::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => Core::FinElim {
                level: *level,
                motive: self.core(motive, scope)?,
                zero: self.core(zero, scope)?,
                step: self.core(step, scope)?,
                bound: self.core(bound, scope)?,
                scrutinee: self.core(scrutinee, scope)?,
            },
            Term::Fin0Elim { ty, absurd } => Core::Fin0Elim {
                ty: self.core(ty, scope)?,
                absurd: self.core(absurd, scope)?,
            },
            Term::Succ(n) => Core::Succ(self.core(n, scope)?),
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Core::NatElim {
                level: *level,
                motive: self.core(motive, scope)?,
                zero: self.core(zero, scope)?,
                step: self.core(step, scope)?,
                scrutinee: self.core(scrutinee, scope)?,
            },
            Term::Meta(id, _) => return Err(Error::UnsolvedMeta { id: *id }),
            Term::App(f, x) => Core::App {
                function: self.core(f, scope)?,
                argument: self.core(x, scope)?,
            },
            Term::Pi {
                id,
                plicity,
                domain,
                body,
            }
            | Term::Lam {
                id,
                plicity,
                domain,
                body,
            } => {
                let domain = self.core(domain, scope)?;
                scope.push(*id);
                let body = self.core(body, scope)?;
                scope.pop();
                if matches!(term.as_ref(), Term::Pi { .. }) {
                    Core::Pi {
                        relevance: plicity.relevance(),
                        domain,
                        codomain: body,
                    }
                } else {
                    Core::Lam {
                        relevance: plicity.relevance(),
                        domain,
                        body,
                    }
                }
            }
        }
        .arc())
    }

    pub(super) fn import_core(&mut self, term: &Tm, scope: &mut Vec<Id>) -> Result<T, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
            Core::Global(id) => {
                self.kernel.definition(*id)?;
                Term::Global(*id)
            }
            Core::Var(i) => {
                let index = scope
                    .len()
                    .checked_sub(i.saturating_add(1))
                    .ok_or(Error::ScopeEscape)?;
                Term::Local(scope[index])
            }
            Core::Universe(l) => Term::Universe(*l),
            Core::Nat => Term::Nat,
            Core::Zero => Term::Zero,
            Core::App { function, argument } => Term::App(
                self.import_core(function, scope)?,
                self.import_core(argument, scope)?,
            ),
            Core::Let { ty, value, body } => {
                let domain = self.import_core(ty, scope)?;
                let value = self.import_core(value, scope)?;
                let id = self.fresh();
                scope.push(id);
                let body = self.import_core(body, scope)?;
                scope.pop();
                Term::App(
                    Term::Lam {
                        id,
                        plicity: Plicity::Explicit,
                        domain,
                        body,
                    }
                    .arc(),
                    value,
                )
            }
            Core::Sigma { domain, codomain } => {
                let domain = self.import_core(domain, scope)?;
                let id = self.fresh();
                scope.push(id);
                let body = self.import_core(codomain, scope)?;
                scope.pop();
                Term::Sigma { id, domain, body }
            }
            Core::Pi {
                relevance,
                domain,
                codomain: body,
            }
            | Core::Lam {
                relevance,
                domain,
                body,
            } => {
                let domain = self.import_core(domain, scope)?;
                let id = self.fresh();
                scope.push(id);
                let body = self.import_core(body, scope)?;
                scope.pop();
                let plicity = match relevance {
                    deppy_core::Relevance::Erased => Plicity::Implicit,
                    deppy_core::Relevance::Runtime => Plicity::Explicit,
                };
                if matches!(term.as_ref(), Core::Pi { .. }) {
                    Term::Pi {
                        id,
                        plicity,
                        domain,
                        body,
                    }
                } else {
                    Term::Lam {
                        id,
                        plicity,
                        domain,
                        body,
                    }
                }
            }
            Core::Succ(x) => Term::Succ(self.import_core(x, scope)?),
            Core::Fst(x) => Term::Fst(self.import_core(x, scope)?),
            Core::Snd(x) => Term::Snd(self.import_core(x, scope)?),
            Core::Data { op, arguments } => Term::Data {
                op: *op,
                arguments: arguments
                    .iter()
                    .map(|x| self.import_core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Core::Inductive { id, parameters } => Term::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.import_core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Core::Constructor {
                id,
                parameters,
                fields,
            } => Term::Constructor {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.import_core(x, scope))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.import_core(x, scope))
                    .collect::<Result<_, _>>()?,
            },
            Core::Elim {
                id,
                parameters,
                level,
                motive,
                branch,
                scrutinee,
            } => Term::Elim {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.import_core(x, scope))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.import_core(motive, scope)?,
                branch: self.import_core(branch, scope)?,
                scrutinee: self.import_core(scrutinee, scope)?,
            },
            Core::Eq { ty, left, right } => Term::Eq {
                ty: self.import_core(ty, scope)?,
                left: self.import_core(left, scope)?,
                right: self.import_core(right, scope)?,
            },
            Core::Refl { ty, value } => Term::Refl {
                ty: self.import_core(ty, scope)?,
                value: self.import_core(value, scope)?,
            },
            Core::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => Term::J {
                level: *level,
                ty: self.import_core(ty, scope)?,
                left: self.import_core(left, scope)?,
                motive: self.import_core(motive, scope)?,
                base: self.import_core(base, scope)?,
                right: self.import_core(right, scope)?,
                proof: self.import_core(proof, scope)?,
            },
            Core::Vec { ty, len } => Term::Vec {
                ty: self.import_core(ty, scope)?,
                len: self.import_core(len, scope)?,
            },
            Core::VNil { ty } => Term::VNil {
                ty: self.import_core(ty, scope)?,
            },
            Core::VCons {
                ty,
                len,
                head,
                tail,
            } => Term::VCons {
                ty: self.import_core(ty, scope)?,
                len: self.import_core(len, scope)?,
                head: self.import_core(head, scope)?,
                tail: self.import_core(tail, scope)?,
            },
            Core::Fin { bound } => Term::Fin {
                bound: self.import_core(bound, scope)?,
            },
            Core::FZ { bound } => Term::FZ {
                bound: self.import_core(bound, scope)?,
            },
            Core::FS { bound, pred } => Term::FS {
                bound: self.import_core(bound, scope)?,
                pred: self.import_core(pred, scope)?,
            },
            Core::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => Term::VecElim {
                level: *level,
                ty: self.import_core(ty, scope)?,
                motive: self.import_core(motive, scope)?,
                nil: self.import_core(nil, scope)?,
                cons: self.import_core(cons, scope)?,
                len: self.import_core(len, scope)?,
                scrutinee: self.import_core(scrutinee, scope)?,
            },
            Core::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => Term::FinElim {
                level: *level,
                motive: self.import_core(motive, scope)?,
                zero: self.import_core(zero, scope)?,
                step: self.import_core(step, scope)?,
                bound: self.import_core(bound, scope)?,
                scrutinee: self.import_core(scrutinee, scope)?,
            },
            Core::Fin0Elim { ty, absurd } => Term::Fin0Elim {
                ty: self.import_core(ty, scope)?,
                absurd: self.import_core(absurd, scope)?,
            },
            Core::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Term::NatElim {
                level: *level,
                motive: self.import_core(motive, scope)?,
                zero: self.import_core(zero, scope)?,
                step: self.import_core(step, scope)?,
                scrutinee: self.import_core(scrutinee, scope)?,
            },
            Core::Pair { ty, fst, snd } => Term::Pair {
                ty: self.import_core(ty, scope)?,
                fst: self.import_core(fst, scope)?,
                snd: self.import_core(snd, scope)?,
            },
        }
        .arc())
    }
    pub(crate) fn finish(&mut self, term: T, ty: T, kernel: &Kernel) -> Result<Elaborated, Error> {
        if !self.user_goals.is_empty() {
            let mut goals = Vec::new();
            for (id, name, location, context, expected) in self.user_goals.clone() {
                let expected = self.zonk(&expected)?;
                let mut locals = Vec::new();
                for local in &context {
                    let ty = self.zonk(&local.ty)?;
                    let value = local.value.as_ref().map(|v| self.zonk(v)).transpose()?;
                    locals.push(crate::GoalLocal {
                        name: super::state::display_name(&local.name),
                        ty: self.describe(&ty, &context),
                        value: value.map(|v| self.describe(&v, &context)),
                    });
                }
                goals.push(crate::Goal {
                    id,
                    name,
                    location,
                    context: locals,
                    expected: self.describe(&expected, &context),
                });
            }
            return Err(Error::Goals(goals));
        }
        // Validate every meta, including ones removed by beta reduction.
        for id in 0..self.metas.len() {
            let meta = self.metas[id].clone();
            let mut solution = meta.solution.ok_or(Error::UnsolvedMeta { id })?;
            let mut expected = meta.expected;
            for local in meta.telescope.iter().rev() {
                solution = Term::Lam {
                    id: local.id,
                    plicity: Plicity::Explicit,
                    domain: local.ty.clone(),
                    body: solution,
                }
                .arc();
                expected = Term::Pi {
                    id: local.id,
                    plicity: Plicity::Explicit,
                    domain: local.ty.clone(),
                    body: expected,
                }
                .arc();
            }
            let solution = self.expand(&solution)?;
            let expected = self.expand(&expected)?;
            let solution = self.core(&solution, &mut vec![])?;
            let expected = self.core(&expected, &mut vec![])?;
            kernel.check(&solution, &expected)?;
        }
        let term = self.expand(&term)?;
        let ty = self.expand(&ty)?;
        let term = self.core(&term, &mut vec![])?;
        let ty = self.core(&ty, &mut vec![])?;
        kernel.check(&term, &ty)?;
        Ok(Elaborated { term, ty })
    }
}
