//! Capture-avoiding substitution over named terms.
use super::super::*;

impl State {
    /// Capture-avoiding simultaneous substitution; unaffected subterms stay shared.
    pub(in crate::solve) fn subst(&mut self, term: &T, map: &HashMap<Id, T>) -> Result<T, Error> {
        self.subst_rewrite(term, map, None)
    }

    /// Freshen affected binders to prevent replacement capture.
    pub(in crate::solve) fn subst_rewrite(
        &mut self,
        term: &T,
        map: &HashMap<Id, T>,
        rule: Option<(&T, &T)>,
    ) -> Result<T, Error> {
        self.subst_cached(term, map, rule, &mut HashMap::new())
    }

    fn subst_cached(
        &mut self,
        term: &T,
        map: &HashMap<Id, T>,
        rule: Option<(&T, &T)>,
        cache: &mut HashMap<usize, T>,
    ) -> Result<T, Error> {
        self.tick()?;
        if let Some((pattern, replacement)) = rule {
            // Rewrite callers supply fully resolved terms, so conversion here
            // cannot solve metavariables. It also compares alpha-renamed binders.
            match self.unify(term, pattern) {
                Ok(()) => return Ok(replacement.clone()),
                Err(Error::CannotUnify) => {}
                Err(error) => return Err(error),
            }
        }
        if rule.is_none()
            && self
                .free_locals(term)?
                .iter()
                .all(|id| !map.contains_key(id))
        {
            return Ok(term.clone());
        }
        let key = std::sync::Arc::as_ptr(term) as usize;
        if let Some(result) = cache.get(&key) {
            return Ok(result.clone());
        }
        let result = match term.as_ref() {
            Term::Data { op, arguments } => Term::Data {
                op: *op,
                arguments: arguments
                    .iter()
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
            },
            Term::Inductive { id, parameters } => Term::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
            },
            Term::Constructor {
                id,
                parameters,
                fields,
            } => Term::Constructor {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
            },
            Term::Elim {
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
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.subst_cached(motive, map, rule, cache)?,
                branch: self.subst_cached(branch, map, rule, cache)?,
                scrutinee: self.subst_cached(scrutinee, map, rule, cache)?,
            },
            Term::Fst(p) => Term::Fst(self.subst_cached(p, map, rule, cache)?),
            Term::Snd(p) => Term::Snd(self.subst_cached(p, map, rule, cache)?),
            Term::Pair { ty, fst, snd } => Term::Pair {
                ty: self.subst_cached(ty, map, rule, cache)?,
                fst: self.subst_cached(fst, map, rule, cache)?,
                snd: self.subst_cached(snd, map, rule, cache)?,
            },
            Term::Sigma { id, domain, body } => {
                let domain = self.subst_cached(domain, map, rule, cache)?;
                let new_id = self.fresh();
                let mut map = map.clone();
                map.insert(*id, Term::Local(new_id).arc());
                Term::Sigma {
                    id: new_id,
                    domain,
                    body: self.subst_cached(body, &map, rule, &mut HashMap::new())?,
                }
            }
            Term::Defined { id, value } => {
                if let Some(replacement) = map.get(id) {
                    return Ok(replacement.clone());
                }
                Term::Defined {
                    id: *id,
                    value: self.subst_cached(value, map, rule, cache)?,
                }
            }
            Term::Global(_) => return Ok(term.clone()),
            Term::Local(id) => return Ok(map.get(id).cloned().unwrap_or_else(|| term.clone())),
            Term::Universe(_) | Term::Nat | Term::Zero => return Ok(term.clone()),
            Term::Eq { ty, left, right } => Term::Eq {
                ty: self.subst_cached(ty, map, rule, cache)?,
                left: self.subst_cached(left, map, rule, cache)?,
                right: self.subst_cached(right, map, rule, cache)?,
            },
            Term::Refl { ty, value } => Term::Refl {
                ty: self.subst_cached(ty, map, rule, cache)?,
                value: self.subst_cached(value, map, rule, cache)?,
            },
            Term::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => Term::J {
                level: *level,
                ty: self.subst_cached(ty, map, rule, cache)?,
                left: self.subst_cached(left, map, rule, cache)?,
                motive: self.subst_cached(motive, map, rule, cache)?,
                base: self.subst_cached(base, map, rule, cache)?,
                right: self.subst_cached(right, map, rule, cache)?,
                proof: self.subst_cached(proof, map, rule, cache)?,
            },
            Term::Vec { ty, len } => Term::Vec {
                ty: self.subst_cached(ty, map, rule, cache)?,
                len: self.subst_cached(len, map, rule, cache)?,
            },
            Term::VNil { ty } => Term::VNil {
                ty: self.subst_cached(ty, map, rule, cache)?,
            },
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => Term::VCons {
                ty: self.subst_cached(ty, map, rule, cache)?,
                len: self.subst_cached(len, map, rule, cache)?,
                head: self.subst_cached(head, map, rule, cache)?,
                tail: self.subst_cached(tail, map, rule, cache)?,
            },
            Term::Fin { bound } => Term::Fin {
                bound: self.subst_cached(bound, map, rule, cache)?,
            },
            Term::FZ { bound } => Term::FZ {
                bound: self.subst_cached(bound, map, rule, cache)?,
            },
            Term::FS { bound, pred } => Term::FS {
                bound: self.subst_cached(bound, map, rule, cache)?,
                pred: self.subst_cached(pred, map, rule, cache)?,
            },
            Term::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => Term::VecElim {
                level: *level,
                ty: self.subst_cached(ty, map, rule, cache)?,
                motive: self.subst_cached(motive, map, rule, cache)?,
                nil: self.subst_cached(nil, map, rule, cache)?,
                cons: self.subst_cached(cons, map, rule, cache)?,
                len: self.subst_cached(len, map, rule, cache)?,
                scrutinee: self.subst_cached(scrutinee, map, rule, cache)?,
            },
            Term::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => Term::FinElim {
                level: *level,
                motive: self.subst_cached(motive, map, rule, cache)?,
                zero: self.subst_cached(zero, map, rule, cache)?,
                step: self.subst_cached(step, map, rule, cache)?,
                bound: self.subst_cached(bound, map, rule, cache)?,
                scrutinee: self.subst_cached(scrutinee, map, rule, cache)?,
            },
            Term::Fin0Elim { ty, absurd } => Term::Fin0Elim {
                ty: self.subst_cached(ty, map, rule, cache)?,
                absurd: self.subst_cached(absurd, map, rule, cache)?,
            },
            Term::Succ(n) => Term::Succ(self.subst_cached(n, map, rule, cache)?),
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Term::NatElim {
                level: *level,
                motive: self.subst_cached(motive, map, rule, cache)?,
                zero: self.subst_cached(zero, map, rule, cache)?,
                step: self.subst_cached(step, map, rule, cache)?,
                scrutinee: self.subst_cached(scrutinee, map, rule, cache)?,
            },
            Term::App(f, x) => Term::App(
                self.subst_cached(f, map, rule, cache)?,
                self.subst_cached(x, map, rule, cache)?,
            ),
            Term::Meta(id, args) => Term::Meta(
                *id,
                args.iter()
                    .map(|x| self.subst_cached(x, map, rule, cache))
                    .collect::<Result<_, _>>()?,
            ),
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
                let domain = self.subst_cached(domain, map, rule, cache)?;
                let new_id = self.fresh();
                let mut map = map.clone();
                map.insert(*id, Term::Local(new_id).arc());
                let body = self.subst_cached(body, &map, rule, &mut HashMap::new())?;
                if matches!(term.as_ref(), Term::Pi { .. }) {
                    Term::Pi {
                        id: new_id,
                        plicity: *plicity,
                        domain,
                        body,
                    }
                } else {
                    Term::Lam {
                        id: new_id,
                        plicity: *plicity,
                        domain,
                        body,
                    }
                }
            }
        }
        .arc();
        cache.insert(key, result.clone());
        Ok(result)
    }
    pub(in crate::solve) fn replace(&mut self, term: &T, id: Id, arg: T) -> Result<T, Error> {
        self.subst(term, &HashMap::from([(id, arg)]))
    }
}
