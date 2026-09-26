use super::*;

impl State {
    /// Capture-avoiding simultaneous substitution; unaffected subterms stay shared.
    pub(super) fn subst(&mut self, term: &T, map: &HashMap<Id, T>) -> Result<T, Error> {
        self.subst_rewrite(term, map, None)
    }

    /// Freshen affected binders to prevent replacement capture.
    pub(super) fn subst_rewrite(
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
    pub(super) fn replace(&mut self, term: &T, id: Id, arg: T) -> Result<T, Error> {
        self.subst(term, &HashMap::from([(id, arg)]))
    }

    pub(super) fn whnf(&mut self, term: &T) -> Result<T, Error> {
        self.tick()?;
        match term.as_ref() {
            Term::Defined { value, .. } => self.whnf(value),
            Term::Data {
                op: deppy_core::DataOp::Eliminate(id, level),
                arguments,
            } => {
                let decl = self.kernel.data_declaration(*id)?.clone();
                let p = decl.parameters.len();
                let i = decl.indices.len();
                let scrutinee = self.whnf(arguments.last().ok_or(Error::CannotUnify)?)?;
                if let Term::Data {
                    op: deppy_core::DataOp::Constructor(other, c),
                    arguments: fields,
                } = scrutinee.as_ref()
                {
                    if other != id {
                        return Err(Error::CannotUnify);
                    }
                    let ctor = decl.constructors.get(*c).ok_or(Error::CannotUnify)?;
                    let motive = arguments[p + i].clone();
                    let branches = arguments[p + i + 1..arguments.len() - 1].to_vec();
                    let mut result = branches[*c].clone();
                    for field in &fields[p..] {
                        result = Term::App(result, field.clone()).arc();
                    }
                    for (f, ty) in ctor.fields.iter().enumerate() {
                        let mut scope = (0..p + f).map(|_| self.fresh()).collect::<Vec<_>>();
                        let imported = self.import_core(ty, &mut scope)?;
                        let map = scope
                            .into_iter()
                            .zip(fields[..p + f].iter().cloned())
                            .collect();
                        let ty = self.subst(&imported, &map)?;
                        if let Some(ih) = self.data_hypothesis(
                            *id,
                            *level,
                            &ty,
                            fields[p + f].clone(),
                            &motive,
                            &branches,
                        )? {
                            result = Term::App(result, ih).arc();
                        }
                    }
                    self.whnf(&result)
                } else {
                    let mut arguments = arguments.clone();
                    *arguments.last_mut().unwrap() = scrutinee;
                    Ok(Term::Data {
                        op: deppy_core::DataOp::Eliminate(*id, *level),
                        arguments,
                    }
                    .arc())
                }
            }
            Term::Global(id) => {
                let Some(body) = self.kernel.definition(*id)?.unfolding_body().cloned() else {
                    return Ok(term.clone());
                };
                let body = self.import_core(&body, &mut vec![])?;
                self.whnf(&body)
            }
            Term::Elim {
                id,
                parameters,
                level,
                motive,
                branch,
                scrutinee,
            } => {
                let scrutinee = self.whnf(scrutinee)?;
                if let Term::Constructor { fields, .. } = scrutinee.as_ref() {
                    let result = fields
                        .iter()
                        .fold(branch.clone(), |f, x| Term::App(f, x.clone()).arc());
                    self.whnf(&result)
                } else {
                    Ok(Term::Elim {
                        id: *id,
                        parameters: parameters.clone(),
                        level: *level,
                        motive: motive.clone(),
                        branch: branch.clone(),
                        scrutinee,
                    }
                    .arc())
                }
            }
            Term::Fst(p) | Term::Snd(p) => {
                let p = self.whnf(p)?;
                if let Term::Pair { fst, snd, .. } = p.as_ref() {
                    self.whnf(if matches!(term.as_ref(), Term::Fst(_)) {
                        fst
                    } else {
                        snd
                    })
                } else {
                    Ok(if matches!(term.as_ref(), Term::Fst(_)) {
                        Term::Fst(p)
                    } else {
                        Term::Snd(p)
                    }
                    .arc())
                }
            }
            Term::Meta(id, args) => {
                let meta = self.metas[*id].clone();
                if let Some(solution) = meta.solution {
                    let map = meta
                        .telescope
                        .iter()
                        .zip(args)
                        .map(|(x, arg)| (x.id, arg.clone()))
                        .collect();
                    let instantiated = self.subst(&solution, &map)?;
                    self.whnf(&instantiated)
                } else {
                    Ok(term.clone())
                }
            }
            Term::App(f, x) => {
                let f = self.whnf(f)?;
                if let Term::Lam { id, body, .. } = f.as_ref() {
                    let body = self.replace(body, *id, x.clone())?;
                    self.whnf(&body)
                } else {
                    Ok(Term::App(f, x.clone()).arc())
                }
            }
            Term::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => {
                let proof = self.whnf(proof)?;
                if matches!(proof.as_ref(), Term::Refl { .. }) {
                    self.whnf(base)
                } else {
                    Ok(Term::J {
                        level: *level,
                        ty: ty.clone(),
                        left: left.clone(),
                        motive: motive.clone(),
                        base: base.clone(),
                        right: right.clone(),
                        proof,
                    }
                    .arc())
                }
            }
            Term::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => {
                let xs = self.whnf(scrutinee)?;
                match xs.as_ref() {
                    Term::VNil { .. } => self.whnf(nil),
                    Term::VCons {
                        len, head, tail, ..
                    } => {
                        let ih = Term::VecElim {
                            level: *level,
                            ty: ty.clone(),
                            motive: motive.clone(),
                            nil: nil.clone(),
                            cons: cons.clone(),
                            len: len.clone(),
                            scrutinee: tail.clone(),
                        }
                        .arc();
                        let branch = app2(cons.clone(), len.clone(), head.clone());
                        self.whnf(&app2(branch, tail.clone(), ih))
                    }
                    _ => Ok(Term::VecElim {
                        level: *level,
                        ty: ty.clone(),
                        motive: motive.clone(),
                        nil: nil.clone(),
                        cons: cons.clone(),
                        len: len.clone(),
                        scrutinee: xs,
                    }
                    .arc()),
                }
            }
            Term::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => {
                let index = self.whnf(scrutinee)?;
                match index.as_ref() {
                    Term::FZ { bound } => self.whnf(&Term::App(zero.clone(), bound.clone()).arc()),
                    Term::FS { bound, pred } => {
                        let ih = Term::FinElim {
                            level: *level,
                            motive: motive.clone(),
                            zero: zero.clone(),
                            step: step.clone(),
                            bound: bound.clone(),
                            scrutinee: pred.clone(),
                        }
                        .arc();
                        self.whnf(
                            &Term::App(app2(step.clone(), bound.clone(), pred.clone()), ih).arc(),
                        )
                    }
                    _ => Ok(Term::FinElim {
                        level: *level,
                        motive: motive.clone(),
                        zero: zero.clone(),
                        step: step.clone(),
                        bound: bound.clone(),
                        scrutinee: index,
                    }
                    .arc()),
                }
            }
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => {
                let n = self.whnf(scrutinee)?;
                match n.as_ref() {
                    Term::Zero => self.whnf(zero),
                    Term::Succ(pred) => {
                        let ih = Term::NatElim {
                            level: *level,
                            motive: motive.clone(),
                            zero: zero.clone(),
                            step: step.clone(),
                            scrutinee: pred.clone(),
                        }
                        .arc();
                        self.whnf(&Term::App(Term::App(step.clone(), pred.clone()).arc(), ih).arc())
                    }
                    _ => Ok(Term::NatElim {
                        level: *level,
                        motive: motive.clone(),
                        zero: zero.clone(),
                        step: step.clone(),
                        scrutinee: n,
                    }
                    .arc()),
                }
            }
            _ => Ok(term.clone()),
        }
    }

    fn data_hypothesis(
        &mut self,
        family: u64,
        level: u32,
        ty: &T,
        field: T,
        motive: &T,
        branches: &[T],
    ) -> Result<Option<T>, Error> {
        self.tick()?;
        let ty = self.whnf(ty)?;
        match ty.as_ref() {
            Term::Data {
                op: deppy_core::DataOp::Type(id),
                arguments,
            } if *id == family => {
                let mut arguments = arguments.clone();
                arguments.push(motive.clone());
                arguments.extend_from_slice(branches);
                arguments.push(field);
                Ok(Some(
                    Term::Data {
                        op: deppy_core::DataOp::Eliminate(family, level),
                        arguments,
                    }
                    .arc(),
                ))
            }
            Term::Pi {
                id,
                plicity,
                domain,
                body,
            } => {
                let argument = Term::Local(*id).arc();
                Ok(self
                    .data_hypothesis(
                        family,
                        level,
                        body,
                        Term::App(field, argument).arc(),
                        motive,
                        branches,
                    )?
                    .map(|body| {
                        Term::Lam {
                            id: *id,
                            plicity: *plicity,
                            domain: domain.clone(),
                            body,
                        }
                        .arc()
                    }))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn zonk(&mut self, term: &T) -> Result<T, Error> {
        let term = self.whnf(term)?;
        Ok(match term.as_ref() {
            Term::Defined { id, value } => Term::Defined {
                id: *id,
                value: self.zonk(value)?,
            },
            Term::Data { op, arguments } => Term::Data {
                op: *op,
                arguments: arguments
                    .iter()
                    .map(|x| self.zonk(x))
                    .collect::<Result<_, _>>()?,
            },
            Term::Inductive { id, parameters } => Term::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.zonk(x))
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
                    .map(|x| self.zonk(x))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.zonk(x))
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
                    .map(|x| self.zonk(x))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.zonk(motive)?,
                branch: self.zonk(branch)?,
                scrutinee: self.zonk(scrutinee)?,
            },
            Term::Fst(p) => Term::Fst(self.zonk(p)?),
            Term::Snd(p) => Term::Snd(self.zonk(p)?),
            Term::Pair { ty, fst, snd } => Term::Pair {
                ty: self.zonk(ty)?,
                fst: self.zonk(fst)?,
                snd: self.zonk(snd)?,
            },
            Term::Sigma { id, domain, body } => Term::Sigma {
                id: *id,
                domain: self.zonk(domain)?,
                body: self.zonk(body)?,
            },
            Term::Global(_) | Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => {
                return Ok(term)
            }
            Term::Eq { ty, left, right } => Term::Eq {
                ty: self.zonk(ty)?,
                left: self.zonk(left)?,
                right: self.zonk(right)?,
            },
            Term::Refl { ty, value } => Term::Refl {
                ty: self.zonk(ty)?,
                value: self.zonk(value)?,
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
                ty: self.zonk(ty)?,
                left: self.zonk(left)?,
                motive: self.zonk(motive)?,
                base: self.zonk(base)?,
                right: self.zonk(right)?,
                proof: self.zonk(proof)?,
            },
            Term::Vec { ty, len } => Term::Vec {
                ty: self.zonk(ty)?,
                len: self.zonk(len)?,
            },
            Term::VNil { ty } => Term::VNil { ty: self.zonk(ty)? },
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => Term::VCons {
                ty: self.zonk(ty)?,
                len: self.zonk(len)?,
                head: self.zonk(head)?,
                tail: self.zonk(tail)?,
            },
            Term::Fin { bound } => Term::Fin {
                bound: self.zonk(bound)?,
            },
            Term::FZ { bound } => Term::FZ {
                bound: self.zonk(bound)?,
            },
            Term::FS { bound, pred } => Term::FS {
                bound: self.zonk(bound)?,
                pred: self.zonk(pred)?,
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
                ty: self.zonk(ty)?,
                motive: self.zonk(motive)?,
                nil: self.zonk(nil)?,
                cons: self.zonk(cons)?,
                len: self.zonk(len)?,
                scrutinee: self.zonk(scrutinee)?,
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
                motive: self.zonk(motive)?,
                zero: self.zonk(zero)?,
                step: self.zonk(step)?,
                bound: self.zonk(bound)?,
                scrutinee: self.zonk(scrutinee)?,
            },
            Term::Fin0Elim { ty, absurd } => Term::Fin0Elim {
                ty: self.zonk(ty)?,
                absurd: self.zonk(absurd)?,
            },
            Term::Succ(n) => Term::Succ(self.zonk(n)?),
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Term::NatElim {
                level: *level,
                motive: self.zonk(motive)?,
                zero: self.zonk(zero)?,
                step: self.zonk(step)?,
                scrutinee: self.zonk(scrutinee)?,
            },
            Term::App(f, x) => Term::App(self.zonk(f)?, self.zonk(x)?),
            Term::Meta(id, args) => Term::Meta(
                *id,
                args.iter()
                    .map(|x| self.zonk(x))
                    .collect::<Result<_, _>>()?,
            ),
            Term::Pi {
                id,
                plicity,
                domain,
                body,
            } => Term::Pi {
                id: *id,
                plicity: *plicity,
                domain: self.zonk(domain)?,
                body: self.zonk(body)?,
            },
            Term::Lam {
                id,
                plicity,
                domain,
                body,
            } => Term::Lam {
                id: *id,
                plicity: *plicity,
                domain: self.zonk(domain)?,
                body: self.zonk(body)?,
            },
        }
        .arc())
    }

    // Resolve metas without reducing applications. The independent kernel must
    // see even ill-typed subterms that beta reduction could otherwise discard.
    pub(super) fn expand(&mut self, term: &T) -> Result<T, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
            Term::Defined { id, value } => Term::Defined {
                id: *id,
                value: self.expand(value)?,
            },
            Term::Data { op, arguments } => Term::Data {
                op: *op,
                arguments: arguments
                    .iter()
                    .map(|x| self.expand(x))
                    .collect::<Result<_, _>>()?,
            },
            Term::Inductive { id, parameters } => Term::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.expand(x))
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
                    .map(|x| self.expand(x))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.expand(x))
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
                    .map(|x| self.expand(x))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.expand(motive)?,
                branch: self.expand(branch)?,
                scrutinee: self.expand(scrutinee)?,
            },
            Term::Fst(p) => Term::Fst(self.expand(p)?),
            Term::Snd(p) => Term::Snd(self.expand(p)?),
            Term::Pair { ty, fst, snd } => Term::Pair {
                ty: self.expand(ty)?,
                fst: self.expand(fst)?,
                snd: self.expand(snd)?,
            },
            Term::Sigma { id, domain, body } => Term::Sigma {
                id: *id,
                domain: self.expand(domain)?,
                body: self.expand(body)?,
            },
            Term::Global(_) | Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => {
                return Ok(term.clone())
            }
            Term::Meta(id, args) => {
                let meta = self.metas[*id].clone();
                let solution = meta.solution.ok_or(Error::UnsolvedMeta { id: *id })?;
                let map = meta
                    .telescope
                    .iter()
                    .zip(args)
                    .map(|(x, arg)| (x.id, arg.clone()))
                    .collect();
                let solution = self.subst(&solution, &map)?;
                return self.expand(&solution);
            }
            Term::Eq { ty, left, right } => Term::Eq {
                ty: self.expand(ty)?,
                left: self.expand(left)?,
                right: self.expand(right)?,
            },
            Term::Refl { ty, value } => Term::Refl {
                ty: self.expand(ty)?,
                value: self.expand(value)?,
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
                ty: self.expand(ty)?,
                left: self.expand(left)?,
                motive: self.expand(motive)?,
                base: self.expand(base)?,
                right: self.expand(right)?,
                proof: self.expand(proof)?,
            },
            Term::Vec { ty, len } => Term::Vec {
                ty: self.expand(ty)?,
                len: self.expand(len)?,
            },
            Term::VNil { ty } => Term::VNil {
                ty: self.expand(ty)?,
            },
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => Term::VCons {
                ty: self.expand(ty)?,
                len: self.expand(len)?,
                head: self.expand(head)?,
                tail: self.expand(tail)?,
            },
            Term::Fin { bound } => Term::Fin {
                bound: self.expand(bound)?,
            },
            Term::FZ { bound } => Term::FZ {
                bound: self.expand(bound)?,
            },
            Term::FS { bound, pred } => Term::FS {
                bound: self.expand(bound)?,
                pred: self.expand(pred)?,
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
                ty: self.expand(ty)?,
                motive: self.expand(motive)?,
                nil: self.expand(nil)?,
                cons: self.expand(cons)?,
                len: self.expand(len)?,
                scrutinee: self.expand(scrutinee)?,
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
                motive: self.expand(motive)?,
                zero: self.expand(zero)?,
                step: self.expand(step)?,
                bound: self.expand(bound)?,
                scrutinee: self.expand(scrutinee)?,
            },
            Term::Fin0Elim { ty, absurd } => Term::Fin0Elim {
                ty: self.expand(ty)?,
                absurd: self.expand(absurd)?,
            },
            Term::Succ(n) => Term::Succ(self.expand(n)?),
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Term::NatElim {
                level: *level,
                motive: self.expand(motive)?,
                zero: self.expand(zero)?,
                step: self.expand(step)?,
                scrutinee: self.expand(scrutinee)?,
            },
            Term::App(f, x) => Term::App(self.expand(f)?, self.expand(x)?),
            Term::Pi {
                id,
                plicity,
                domain,
                body,
            } => Term::Pi {
                id: *id,
                plicity: *plicity,
                domain: self.expand(domain)?,
                body: self.expand(body)?,
            },
            Term::Lam {
                id,
                plicity,
                domain,
                body,
            } => Term::Lam {
                id: *id,
                plicity: *plicity,
                domain: self.expand(domain)?,
                body: self.expand(body)?,
            },
        }
        .arc())
    }
}
