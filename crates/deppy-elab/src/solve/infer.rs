use super::*;

impl State {
    pub(crate) fn type_expr(&mut self, ctx: &Context, expr: &Expr) -> Result<(T, u32), Error> {
        let (term, ty) = self.synth(ctx, expr)?;
        match self.whnf(&ty)?.as_ref() {
            Term::Universe(level) => Ok((term, *level)),
            _ => Err(Error::ExpectedUniverse),
        }
    }

    // Substitute the definition at name lookup. Retain its checked value in an
    // explicit application so even unused definitions reach the kernel recheck.
    fn let_expr(
        &mut self,
        ctx: &Context,
        name: &str,
        annotation: Option<&Expr>,
        value: &Expr,
        body: &Expr,
        expected: Option<&T>,
    ) -> Result<(T, T), Error> {
        let (value, ty) = if let Some(annotation) = annotation {
            let (ty, _) = self.type_expr(ctx, annotation)?;
            (self.check(ctx, value, &ty)?, ty)
        } else {
            self.synth(ctx, value)?
        };
        let (mut inner, id) = self.bind(ctx, name, ty.clone());
        inner.last_mut().unwrap().value = Some(value.clone());
        let (body, result) = if let Some(expected) = expected {
            (self.check(&inner, body, expected)?, expected.clone())
        } else {
            self.synth(&inner, body)?
        };
        Ok((
            Term::App(
                Term::Lam {
                    id,
                    plicity: Plicity::Explicit,
                    domain: ty,
                    body,
                }
                .arc(),
                value,
            )
            .arc(),
            result,
        ))
    }

    pub(crate) fn synth(&mut self, ctx: &Context, expr: &Expr) -> Result<(T, T), Error> {
        self.tick()?;
        match expr {
            Expr::Located {
                location,
                expression,
            } => self.synth(ctx, expression).map_err(|e| e.at(location)),
            Expr::Let {
                name,
                ty,
                value,
                body,
            } => self.let_expr(ctx, name, ty.as_deref(), value, body, None),
            Expr::Recur(_) => Err(Error::InvalidRecursion(
                "self-call outside function lowering".into(),
            )),
            Expr::Core(term) => {
                let ty = self.kernel.infer(term)?;
                let term = self.import_core(term, &mut vec![])?;
                let ty = self.import_core(&ty, &mut vec![])?;
                Ok((term, ty))
            }
            Expr::Sigma {
                name,
                domain,
                codomain,
            } => {
                let (domain, a) = self.type_expr(ctx, domain)?;
                let (ctx, id) = self.bind(ctx, name, domain.clone());
                let (body, b) = self.type_expr(&ctx, codomain)?;
                Ok((
                    Term::Sigma { id, domain, body }.arc(),
                    Term::Universe(a.max(b)).arc(),
                ))
            }
            Expr::Pair { .. } => Err(Error::AnnotationRequired),
            Expr::RecordElim {
                level,
                motive,
                branch,
                value,
            } => {
                let (value, receiver_ty) = self.synth(ctx, value)?;
                let receiver_ty = self.whnf(&receiver_ty)?;
                let Term::Inductive { id, parameters } = receiver_ty.as_ref() else {
                    return Err(Error::ExpectedRecord);
                };
                let function = Expr::Core(self.kernel.eliminator_function(*id, *level)?);
                let (mut function, mut ty) = self.synth(ctx, &function)?;
                for argument in parameters {
                    let head = self.whnf(&ty)?;
                    let Term::Pi { id, body, .. } = head.as_ref() else {
                        return Err(Error::ExpectedFunction);
                    };
                    ty = self.replace(body, *id, argument.clone())?;
                    function = Term::App(function, argument.clone()).arc();
                }
                for argument in [motive.as_ref(), branch.as_ref()] {
                    let head = self.whnf(&ty)?;
                    let Term::Pi {
                        id, domain, body, ..
                    } = head.as_ref()
                    else {
                        return Err(Error::ExpectedFunction);
                    };
                    let argument = self.check(ctx, argument, domain)?;
                    ty = self.replace(body, *id, argument.clone())?;
                    function = Term::App(function, argument).arc();
                }
                let head = self.whnf(&ty)?;
                let Term::Pi {
                    id, domain, body, ..
                } = head.as_ref()
                else {
                    return Err(Error::ExpectedFunction);
                };
                self.unify(domain, &receiver_ty)?;
                let ty = self.replace(body, *id, value.clone())?;
                Ok((Term::App(function, value).arc(), ty))
            }
            Expr::Field { value, name } => {
                let (value, receiver_ty) = self.synth(ctx, value)?;
                let receiver_ty = self.whnf(&receiver_ty)?;
                let Term::Inductive { id, parameters } = receiver_ty.as_ref() else {
                    return Err(Error::ExpectedRecord);
                };
                let projection = self
                    .records
                    .get(id)
                    .ok_or(Error::ExpectedRecord)?
                    .projection(name)?;
                let (mut function, mut ty) = self.synth(ctx, &projection)?;
                // Parameters come from the checked receiver's nominal type, so no
                // candidate guessing or speculative metavariable solving is needed.
                for (index, argument) in
                    parameters.iter().chain(std::iter::once(&value)).enumerate()
                {
                    let head = self.whnf(&ty)?;
                    let Term::Pi {
                        id,
                        plicity,
                        domain,
                        body,
                    } = head.as_ref()
                    else {
                        return Err(Error::ExpectedFunction);
                    };
                    let expected = if index < parameters.len() {
                        Plicity::Implicit
                    } else {
                        Plicity::Explicit
                    };
                    if *plicity != expected {
                        return Err(Error::PlicityMismatch);
                    }
                    if index == parameters.len() {
                        self.unify(domain, &receiver_ty)?;
                    }
                    ty = self.replace(body, *id, argument.clone())?;
                    function = Term::App(function, argument.clone()).arc();
                }
                Ok((function, ty))
            }
            Expr::Fst(p) | Expr::Snd(p) => {
                let (p, ty) = self.synth(ctx, p)?;
                let ty = self.whnf(&ty)?;
                let Term::Sigma { id, domain, body } = ty.as_ref() else {
                    return Err(Error::ExpectedSigma);
                };
                if matches!(expr, Expr::Fst(_)) {
                    Ok((Term::Fst(p).arc(), domain.clone()))
                } else {
                    let ty = self.replace(body, *id, Term::Fst(p.clone()).arc())?;
                    Ok((Term::Snd(p).arc(), ty))
                }
            }
            Expr::Name(name) => {
                if let Some(local) = ctx.iter().rev().find(|x| x.name == *name) {
                    return Ok((
                        local
                            .value
                            .clone()
                            .unwrap_or_else(|| Term::Local(local.id).arc()),
                        local.ty.clone(),
                    ));
                }
                let id = *self
                    .globals
                    .get(name)
                    .ok_or_else(|| Error::UnknownName(name.clone()))?;
                let ty = self.kernel.definition(id)?.ty.clone();
                Ok((Term::Global(id).arc(), self.import_core(&ty, &mut vec![])?))
            }
            Expr::Universe(level) => Ok((
                Term::Universe(*level).arc(),
                Term::Universe(level.checked_add(1).ok_or(Error::UniverseOverflow)?).arc(),
            )),
            Expr::Eq { ty, left, right } => {
                let (ty, level) = self.type_expr(ctx, ty)?;
                let left = self.check(ctx, left, &ty)?;
                let right = self.check(ctx, right, &ty)?;
                Ok((
                    Term::Eq { ty, left, right }.arc(),
                    Term::Universe(level).arc(),
                ))
            }
            Expr::Refl(value) => {
                let (value, ty) = self.synth(ctx, value)?;
                Ok((
                    Term::Refl {
                        ty: ty.clone(),
                        value: value.clone(),
                    }
                    .arc(),
                    Term::Eq {
                        ty,
                        left: value.clone(),
                        right: value,
                    }
                    .arc(),
                ))
            }
            Expr::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => {
                level.checked_add(1).ok_or(Error::UniverseOverflow)?;
                let (ty, _) = self.type_expr(ctx, ty)?;
                let left = self.check(ctx, left, &ty)?;
                let right = self.check(ctx, right, &ty)?;
                let y = self.fresh();
                let p = self.fresh();
                let motive_ty = Term::Pi {
                    id: y,
                    plicity: Plicity::Explicit,
                    domain: ty.clone(),
                    body: Term::Pi {
                        id: p,
                        plicity: Plicity::Explicit,
                        domain: Term::Eq {
                            ty: ty.clone(),
                            left: left.clone(),
                            right: Term::Local(y).arc(),
                        }
                        .arc(),
                        body: Term::Universe(*level).arc(),
                    }
                    .arc(),
                }
                .arc();
                let motive = self.check(ctx, motive, &motive_ty)?;
                let refl = Term::Refl {
                    ty: ty.clone(),
                    value: left.clone(),
                }
                .arc();
                let base_ty = Term::App(Term::App(motive.clone(), left.clone()).arc(), refl).arc();
                let base = self.check(ctx, base, &base_ty)?;
                let proof_ty = Term::Eq {
                    ty: ty.clone(),
                    left: left.clone(),
                    right: right.clone(),
                }
                .arc();
                let proof = self.check(ctx, proof, &proof_ty)?;
                let result = Term::App(
                    Term::App(motive.clone(), right.clone()).arc(),
                    proof.clone(),
                )
                .arc();
                Ok((
                    Term::J {
                        level: *level,
                        ty,
                        left,
                        motive,
                        base,
                        right,
                        proof,
                    }
                    .arc(),
                    result,
                ))
            }
            Expr::Vec { ty, len } => {
                let (ty, level) = self.type_expr(ctx, ty)?;
                let len = self.check(ctx, len, &Term::Nat.arc())?;
                Ok((Term::Vec { ty, len }.arc(), Term::Universe(level).arc()))
            }
            Expr::VNil { ty } => {
                let (ty, _) = self.type_expr(ctx, ty)?;
                Ok((
                    Term::VNil { ty: ty.clone() }.arc(),
                    Term::Vec {
                        ty,
                        len: Term::Zero.arc(),
                    }
                    .arc(),
                ))
            }
            Expr::VCons {
                ty,
                len,
                head,
                tail,
            } => {
                let (ty, _) = self.type_expr(ctx, ty)?;
                let len = self.check(ctx, len, &Term::Nat.arc())?;
                let head = self.check(ctx, head, &ty)?;
                let tail = self.check(
                    ctx,
                    tail,
                    &Term::Vec {
                        ty: ty.clone(),
                        len: len.clone(),
                    }
                    .arc(),
                )?;
                let result = Term::Vec {
                    ty: ty.clone(),
                    len: Term::Succ(len.clone()).arc(),
                }
                .arc();
                Ok((
                    Term::VCons {
                        ty,
                        len,
                        head,
                        tail,
                    }
                    .arc(),
                    result,
                ))
            }
            Expr::Fin { bound } => {
                let bound = self.check(ctx, bound, &Term::Nat.arc())?;
                Ok((Term::Fin { bound }.arc(), Term::Universe(0).arc()))
            }
            Expr::FZ { bound } => {
                let bound = self.check(ctx, bound, &Term::Nat.arc())?;
                Ok((
                    Term::FZ {
                        bound: bound.clone(),
                    }
                    .arc(),
                    Term::Fin {
                        bound: Term::Succ(bound).arc(),
                    }
                    .arc(),
                ))
            }
            Expr::FS { bound, pred } => {
                let bound = self.check(ctx, bound, &Term::Nat.arc())?;
                let pred = self.check(
                    ctx,
                    pred,
                    &Term::Fin {
                        bound: bound.clone(),
                    }
                    .arc(),
                )?;
                let result = Term::Fin {
                    bound: Term::Succ(bound.clone()).arc(),
                }
                .arc();
                Ok((Term::FS { bound, pred }.arc(), result))
            }
            Expr::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => {
                level.checked_add(1).ok_or(Error::UniverseOverflow)?;
                let (ty, _) = self.type_expr(ctx, ty)?;
                let len = self.check(ctx, len, &Term::Nat.arc())?;
                let scrutinee = self.check(
                    ctx,
                    scrutinee,
                    &Term::Vec {
                        ty: ty.clone(),
                        len: len.clone(),
                    }
                    .arc(),
                )?;
                let k = self.fresh();
                let h = self.fresh();
                let t = self.fresh();
                let ih = self.fresh();
                let kval = Term::Local(k).arc();
                let hval = Term::Local(h).arc();
                let tval = Term::Local(t).arc();
                let tail_ty = Term::Vec {
                    ty: ty.clone(),
                    len: kval.clone(),
                }
                .arc();
                let motive_ty = pi(
                    k,
                    Term::Nat.arc(),
                    pi(t, tail_ty.clone(), Term::Universe(*level).arc()),
                );
                let motive = self.check(ctx, motive, &motive_ty)?;
                let nil_ty = app2(
                    motive.clone(),
                    Term::Zero.arc(),
                    Term::VNil { ty: ty.clone() }.arc(),
                );
                let nil = self.check(ctx, nil, &nil_ty)?;
                let ih_ty = app2(motive.clone(), kval.clone(), tval.clone());
                let cons_value = Term::VCons {
                    ty: ty.clone(),
                    len: kval.clone(),
                    head: hval,
                    tail: tval,
                }
                .arc();
                let cons_result = app2(motive.clone(), Term::Succ(kval).arc(), cons_value);
                let cons_ty = pi(
                    k,
                    Term::Nat.arc(),
                    pi(h, ty.clone(), pi(t, tail_ty, pi(ih, ih_ty, cons_result))),
                );
                let cons = self.check(ctx, cons, &cons_ty)?;
                let result = app2(motive.clone(), len.clone(), scrutinee.clone());
                Ok((
                    Term::VecElim {
                        level: *level,
                        ty,
                        motive,
                        nil,
                        cons,
                        len,
                        scrutinee,
                    }
                    .arc(),
                    result,
                ))
            }
            Expr::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => {
                level.checked_add(1).ok_or(Error::UniverseOverflow)?;
                let bound = self.check(ctx, bound, &Term::Nat.arc())?;
                let scrutinee = self.check(
                    ctx,
                    scrutinee,
                    &Term::Fin {
                        bound: bound.clone(),
                    }
                    .arc(),
                )?;
                let k = self.fresh();
                let i = self.fresh();
                let ih = self.fresh();
                let kval = Term::Local(k).arc();
                let ival = Term::Local(i).arc();
                let pred_ty = Term::Fin {
                    bound: kval.clone(),
                }
                .arc();
                let motive_ty = pi(
                    k,
                    Term::Nat.arc(),
                    pi(i, pred_ty.clone(), Term::Universe(*level).arc()),
                );
                let motive = self.check(ctx, motive, &motive_ty)?;
                let zero_ty = pi(
                    k,
                    Term::Nat.arc(),
                    app2(
                        motive.clone(),
                        Term::Succ(kval.clone()).arc(),
                        Term::FZ {
                            bound: kval.clone(),
                        }
                        .arc(),
                    ),
                );
                let zero = self.check(ctx, zero, &zero_ty)?;
                let ih_ty = app2(motive.clone(), kval.clone(), ival.clone());
                let step_value = Term::FS {
                    bound: kval.clone(),
                    pred: ival,
                }
                .arc();
                let step_result = app2(motive.clone(), Term::Succ(kval).arc(), step_value);
                let step_ty = pi(
                    k,
                    Term::Nat.arc(),
                    pi(i, pred_ty, pi(ih, ih_ty, step_result)),
                );
                let step = self.check(ctx, step, &step_ty)?;
                let result = app2(motive.clone(), bound.clone(), scrutinee.clone());
                Ok((
                    Term::FinElim {
                        level: *level,
                        motive,
                        zero,
                        step,
                        bound,
                        scrutinee,
                    }
                    .arc(),
                    result,
                ))
            }
            Expr::Fin0Elim { ty, absurd } => {
                let (ty, _) = self.type_expr(ctx, ty)?;
                let absurd = self.check(
                    ctx,
                    absurd,
                    &Term::Fin {
                        bound: Term::Zero.arc(),
                    }
                    .arc(),
                )?;
                Ok((
                    Term::Fin0Elim {
                        ty: ty.clone(),
                        absurd,
                    }
                    .arc(),
                    ty,
                ))
            }
            Expr::Nat => Ok((Term::Nat.arc(), Term::Universe(0).arc())),
            Expr::Zero => Ok((Term::Zero.arc(), Term::Nat.arc())),
            Expr::Succ(n) => {
                let n = self.check(ctx, n, &Term::Nat.arc())?;
                Ok((Term::Succ(n).arc(), Term::Nat.arc()))
            }
            Expr::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => {
                level.checked_add(1).ok_or(Error::UniverseOverflow)?;
                let motive_ty = Term::Pi {
                    id: self.fresh(),
                    plicity: Plicity::Explicit,
                    domain: Term::Nat.arc(),
                    body: Term::Universe(*level).arc(),
                }
                .arc();
                let motive = self.check(ctx, motive, &motive_ty)?;
                let zero_ty = Term::App(motive.clone(), Term::Zero.arc()).arc();
                let zero = self.check(ctx, zero, &zero_ty)?;
                let n = self.fresh();
                let ih_ty = Term::App(motive.clone(), Term::Local(n).arc()).arc();
                let result_ty =
                    Term::App(motive.clone(), Term::Succ(Term::Local(n).arc()).arc()).arc();
                let step_ty = Term::Pi {
                    id: n,
                    plicity: Plicity::Explicit,
                    domain: Term::Nat.arc(),
                    body: Term::Pi {
                        id: self.fresh(),
                        plicity: Plicity::Explicit,
                        domain: ih_ty,
                        body: result_ty,
                    }
                    .arc(),
                }
                .arc();
                let step = self.check(ctx, step, &step_ty)?;
                let scrutinee = self.check(ctx, scrutinee, &Term::Nat.arc())?;
                let ty = Term::App(motive.clone(), scrutinee.clone()).arc();
                Ok((
                    Term::NatElim {
                        level: *level,
                        motive,
                        zero,
                        step,
                        scrutinee,
                    }
                    .arc(),
                    ty,
                ))
            }
            Expr::Pi {
                name,
                plicity,
                domain,
                codomain,
            } => {
                let (domain, a) = self.type_expr(ctx, domain)?;
                let (ctx, id) = self.bind(ctx, name, domain.clone());
                let (body, b) = self.type_expr(&ctx, codomain)?;
                Ok((
                    Term::Pi {
                        id,
                        plicity: *plicity,
                        domain,
                        body,
                    }
                    .arc(),
                    Term::Universe(a.max(b)).arc(),
                ))
            }
            Expr::Lam {
                name,
                plicity,
                domain,
                body,
            } => {
                let domain = domain.as_ref().ok_or(Error::AnnotationRequired)?;
                let (domain, _) = self.type_expr(ctx, domain)?;
                let (ctx, id) = self.bind(ctx, name, domain.clone());
                let (body, ty) = self.synth(&ctx, body)?;
                Ok((
                    Term::Lam {
                        id,
                        plicity: *plicity,
                        domain: domain.clone(),
                        body,
                    }
                    .arc(),
                    Term::Pi {
                        id,
                        plicity: *plicity,
                        domain,
                        body: ty,
                    }
                    .arc(),
                ))
            }
            Expr::App {
                function,
                argument,
                plicity,
            } => {
                let (mut fun, mut ty) = self.synth(ctx, function)?;
                loop {
                    let head = self.whnf(&ty)?;
                    let Term::Pi {
                        id,
                        plicity: mode,
                        domain,
                        body,
                    } = head.as_ref()
                    else {
                        return Err(Error::ExpectedFunction);
                    };
                    if *plicity == Plicity::Explicit && *mode == Plicity::Implicit {
                        let arg = self.meta(ctx, domain.clone());
                        fun = Term::App(fun, arg.clone()).arc();
                        ty = self.replace(body, *id, arg)?;
                        continue;
                    }
                    if plicity != mode {
                        return Err(Error::PlicityMismatch);
                    }
                    let arg = self.check(ctx, argument, domain)?;
                    let ty = self.replace(body, *id, arg.clone())?;
                    return Ok((Term::App(fun, arg).arc(), ty));
                }
            }
            Expr::Ann { term, ty } => {
                let (ty, _) = self.type_expr(ctx, ty)?;
                Ok((self.check(ctx, term, &ty)?, ty))
            }
            Expr::Hole | Expr::UserHole(_) => Err(Error::AnnotationRequired),
        }
    }

    pub(crate) fn check(&mut self, ctx: &Context, expr: &Expr, expected: &T) -> Result<T, Error> {
        self.tick()?;
        if let Expr::Located {
            location,
            expression,
        } = expr
        {
            let previous = self.location.replace(location.clone());
            let result = self
                .check(ctx, expression, expected)
                .map_err(|e| e.at(location));
            self.location = previous;
            return result;
        }
        if let Expr::Let {
            name,
            ty,
            value,
            body,
        } = expr
        {
            return Ok(self
                .let_expr(ctx, name, ty.as_deref(), value, body, Some(expected))?
                .0);
        }
        if let Expr::UserHole(name) = expr {
            let id = self.metas.len();
            let term = self.meta(ctx, expected.clone());
            self.user_goals.push((
                id,
                name.clone(),
                self.location.clone(),
                ctx.clone(),
                expected.clone(),
            ));
            return Ok(term);
        }
        if matches!(expr, Expr::Hole) {
            return Ok(self.meta(ctx, expected.clone()));
        }
        if let Expr::Pair { fst, snd } = expr {
            let ty = self.whnf(expected)?;
            let Term::Sigma { id, domain, body } = ty.as_ref() else {
                return Err(Error::ExpectedSigma);
            };
            let fst = self.check(ctx, fst, domain)?;
            let second_ty = self.replace(body, *id, fst.clone())?;
            let snd = self.check(ctx, snd, &second_ty)?;
            return Ok(Term::Pair {
                ty: expected.clone(),
                fst,
                snd,
            }
            .arc());
        }
        if let Expr::Refl(value) = expr {
            let expected = self.whnf(expected)?;
            if let Term::Eq { ty, left, right } = expected.as_ref() {
                let value = self.check(ctx, value, ty)?;
                self.unify(&value, left)?;
                self.unify(&value, right)?;
                return Ok(Term::Refl {
                    ty: ty.clone(),
                    value,
                }
                .arc());
            }
        }
        if let Expr::Lam {
            name,
            plicity,
            domain,
            body,
        } = expr
        {
            let ty = self.whnf(expected)?;
            let Term::Pi {
                id: old_id,
                plicity: mode,
                domain: dom,
                body: cod,
            } = ty.as_ref()
            else {
                return Err(Error::ExpectedFunction);
            };
            if plicity != mode {
                return Err(Error::PlicityMismatch);
            }
            if let Some(annotation) = domain {
                let (annotation, _) = self.type_expr(ctx, annotation)?;
                self.unify(&annotation, dom)?;
            }
            let (ctx, id) = self.bind(ctx, name, dom.clone());
            let cod = self.replace(cod, *old_id, Term::Local(id).arc())?;
            let body = self.check(&ctx, body, &cod)?;
            return Ok(Term::Lam {
                id,
                plicity: *plicity,
                domain: dom.clone(),
                body,
            }
            .arc());
        }
        let (term, ty) = self.synth(ctx, expr)?;
        self.unify(&ty, expected).map_err(|error| {
            if self.location.is_some() && matches!(error, Error::CannotUnify) {
                Error::TypeMismatch {
                    expected: self.describe(expected, ctx),
                    actual: self.describe(&ty, ctx),
                }
            } else {
                error
            }
        })?;
        Ok(term)
    }
}
