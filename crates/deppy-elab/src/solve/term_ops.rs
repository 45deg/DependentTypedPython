use super::*;
mod resolution;
mod subst;

impl State {
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
}
