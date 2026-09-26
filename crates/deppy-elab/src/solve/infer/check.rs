//! Check terms against an expected type.
use super::super::*;

impl State {
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
        if let Expr::Cases {
            level,
            value,
            branches,
            generalize,
        } = expr
        {
            return self.cases(ctx, *level, value, branches, generalize, expected);
        }
        if let Expr::Rewrite {
            proof,
            body,
            forward: false,
        } = expr
        {
            return self
                .rewrite_equality(ctx, proof, body, Some(expected))
                .map(|(term, _)| term);
        }
        if let Expr::AutoProof { name, hints } = expr {
            if let Some(proof) = self.auto_proof(ctx, expected, hints)? {
                return Ok(proof);
            }
            return self.check(ctx, &Expr::UserHole(name.clone()), expected);
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
                return Err(self.type_error(
                    ctx,
                    Error::ExpectedSigma,
                    "a dependent pair type",
                    &ty,
                ));
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
            if let Term::Eq { ty, .. } = expected.as_ref() {
                let value = self.check(ctx, value, ty)?;
                let actual = Term::Eq {
                    ty: ty.clone(),
                    left: value.clone(),
                    right: value.clone(),
                }
                .arc();
                self.unify_types(ctx, &actual, &expected)?;
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
                return Err(self.type_error(
                    ctx,
                    Error::ExpectedFunction,
                    "a dependent function type",
                    &ty,
                ));
            };
            if plicity != mode {
                return Err(self.type_error(
                    ctx,
                    Error::PlicityMismatch,
                    "matching explicit/implicit binders",
                    &ty,
                ));
            }
            if let Some(annotation) = domain {
                let (annotation, _) = self.type_expr(ctx, annotation)?;
                self.unify_types(ctx, &annotation, dom)?;
            }
            let (mut ctx, id) = self.bind(ctx, name, dom.clone());
            ctx.last_mut().unwrap().plicity = *plicity;
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
        self.unify_types(ctx, &ty, expected)?;
        Ok(term)
    }
}
