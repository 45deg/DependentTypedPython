//! Resolve metavariables for elaboration and final kernel checking.
use super::super::*;

impl State {
    pub(in crate::solve) fn zonk(&mut self, term: &T) -> Result<T, Error> {
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
    pub(in crate::solve) fn expand(&mut self, term: &T) -> Result<T, Error> {
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
