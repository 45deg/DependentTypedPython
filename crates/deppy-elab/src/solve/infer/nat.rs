//! Elaborate the dependent natural-number eliminator.
use super::super::*;

impl State {
    pub(in crate::solve) fn nat_induction(
        &mut self,
        ctx: &Context,
        level: u32,
        motive: &Expr,
        zero: &Expr,
        step: &Expr,
        scrutinee: T,
    ) -> Result<(T, T), Error> {
        level.checked_add(1).ok_or(Error::UniverseOverflow)?;
        let motive_ty = Term::Pi {
            id: self.fresh(),
            plicity: Plicity::Explicit,
            domain: Term::Nat.arc(),
            body: Term::Universe(level).arc(),
        }
        .arc();
        let motive = self.check(ctx, motive, &motive_ty)?;
        let zero_ty = Term::App(motive.clone(), Term::Zero.arc()).arc();
        let zero = self.check(ctx, zero, &zero_ty)?;
        let n = self.fresh();
        let ih_ty = Term::App(motive.clone(), Term::Local(n).arc()).arc();
        let result_ty = Term::App(motive.clone(), Term::Succ(Term::Local(n).arc()).arc()).arc();
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
        let ty = Term::App(motive.clone(), scrutinee.clone()).arc();
        Ok((
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            }
            .arc(),
            ty,
        ))
    }
}
