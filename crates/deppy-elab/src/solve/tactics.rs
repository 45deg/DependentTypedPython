//! Small proof transformations. Only ordinary equality elimination reaches Core.
use super::*;

impl State {
    fn rewrite_level(&mut self, ctx: &Context, ty: &T) -> Result<u32, Error> {
        let saved = std::mem::take(&mut self.core_domains);
        let result = (|| {
            let mut scope = vec![];
            for local in ctx {
                let domain = self.expand(&local.ty)?;
                let domain = self.core(&domain, &mut scope)?;
                self.core_domains.push(domain);
                scope.push(local.id);
            }
            let ty = self.expand(ty)?;
            let ty = self.core(&ty, &mut scope)?;
            Ok(self.kernel.carrier_universe(&ty, &self.core_domains)?)
        })();
        self.core_domains = saved;
        result
    }

    pub(super) fn rewrite_equality(
        &mut self,
        ctx: &Context,
        proof: &Expr,
        body: &Expr,
        expected: Option<&T>,
    ) -> Result<(T, T), Error> {
        let (proof, equality) = self.synth(ctx, proof)?;
        let equality = self.whnf(&equality)?;
        let Term::Eq { ty, left, right } = equality.as_ref() else {
            return Err(Error::CannotUnify);
        };
        let (base, target) = if let Some(expected) = expected {
            (None, expected.clone())
        } else {
            let (base, target) = self.synth(ctx, body)?;
            (Some(base), target)
        };
        let level = self.rewrite_level(ctx, &target)?;
        let target = self.expand(&target)?;
        let target = self.zonk(&target)?;
        let left = self.expand(left)?;
        let right = self.expand(right)?;
        let left = self.zonk(&left)?;
        let right = self.zonk(&right)?;
        let y = self.fresh();
        let p = self.fresh();
        let local = Term::Local(y).arc();
        let family = self.subst_rewrite(&target, &HashMap::new(), Some((&left, &local)))?;
        let rewritten = self.replace(&family, y, right.clone())?;
        let eq = Term::Eq {
            ty: ty.clone(),
            left: left.clone(),
            right: local,
        }
        .arc();
        let (base, result, motive_body) = if let Some(base) = base {
            (base, rewritten.clone(), family)
        } else {
            // J produces P(right) -> P(left); apply it to the rewritten proof.
            let argument = self.fresh();
            let identity = Term::Lam {
                id: argument,
                plicity: Plicity::Explicit,
                domain: target.clone(),
                body: Term::Local(argument).arc(),
            }
            .arc();
            (
                identity,
                target.clone(),
                pi(argument, family, target.clone()),
            )
        };
        let motive = Term::Lam {
            id: y,
            plicity: Plicity::Explicit,
            domain: ty.clone(),
            body: Term::Lam {
                id: p,
                plicity: Plicity::Explicit,
                domain: eq,
                body: motive_body,
            }
            .arc(),
        }
        .arc();
        let term = Term::J {
            level,
            ty: ty.clone(),
            left,
            motive,
            base,
            right,
            proof,
        }
        .arc();
        let term = if expected.is_some() {
            let body = self.check(ctx, body, &rewritten)?;
            Term::App(term, body).arc()
        } else {
            term
        };
        Ok((term, result))
    }
}
