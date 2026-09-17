use crate::syntax::{Id, Term, T};
use crate::{Elaborated, Error, Expr, Plicity};
use deppy_core::{Kernel, Term as Core, Tm};
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub(crate) struct Local {
    id: Id,
    name: String,
    ty: T,
}
pub(crate) type Context = Vec<Local>;

#[derive(Clone)]
struct Meta {
    telescope: Context,
    expected: T,
    solution: Option<T>,
}

pub(crate) struct State {
    kernel: Kernel,
    next_id: Id,
    remaining: usize,
    metas: Vec<Meta>,
}
impl State {
    pub fn new(remaining: usize) -> Self {
        Self {
            kernel: Kernel::new(remaining),
            next_id: 0,
            remaining,
            metas: vec![],
        }
    }
    pub fn with_kernel(remaining: usize, kernel: Kernel) -> Self {
        Self {
            kernel,
            ..Self::new(remaining)
        }
    }
    fn tick(&mut self) -> Result<(), Error> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Error::BudgetExceeded)?;
        Ok(())
    }
    fn fresh(&mut self) -> Id {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
    fn meta(&mut self, ctx: &Context, expected: T) -> T {
        let id = self.metas.len();
        self.metas.push(Meta {
            telescope: ctx.clone(),
            expected,
            solution: None,
        });
        Term::Meta(id, ctx.iter().map(|x| Term::Local(x.id).arc()).collect()).arc()
    }
    fn bind(&mut self, ctx: &Context, name: &str, ty: T) -> (Context, Id) {
        let id = self.fresh();
        let mut ctx = ctx.clone();
        ctx.push(Local {
            id,
            name: name.to_owned(),
            ty,
        });
        (ctx, id)
    }

    /// Capture-avoiding simultaneous substitution, freshening every binder.
    fn subst(&mut self, term: &T, map: &HashMap<Id, T>) -> Result<T, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
            Term::Inductive { id, parameters } => Term::Inductive {
                id: *id,
                parameters: parameters
                    .iter()
                    .map(|x| self.subst(x, map))
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
                    .map(|x| self.subst(x, map))
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .iter()
                    .map(|x| self.subst(x, map))
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
                    .map(|x| self.subst(x, map))
                    .collect::<Result<_, _>>()?,
                level: *level,
                motive: self.subst(motive, map)?,
                branch: self.subst(branch, map)?,
                scrutinee: self.subst(scrutinee, map)?,
            },
            Term::Fst(p) => Term::Fst(self.subst(p, map)?),
            Term::Snd(p) => Term::Snd(self.subst(p, map)?),
            Term::Pair { ty, fst, snd } => Term::Pair {
                ty: self.subst(ty, map)?,
                fst: self.subst(fst, map)?,
                snd: self.subst(snd, map)?,
            },
            Term::Sigma { id, domain, body } => {
                let domain = self.subst(domain, map)?;
                let new_id = self.fresh();
                let mut map = map.clone();
                map.insert(*id, Term::Local(new_id).arc());
                Term::Sigma {
                    id: new_id,
                    domain,
                    body: self.subst(body, &map)?,
                }
            }
            Term::Local(id) => return Ok(map.get(id).cloned().unwrap_or_else(|| term.clone())),
            Term::Universe(_) | Term::Nat | Term::Zero => return Ok(term.clone()),
            Term::Eq { ty, left, right } => Term::Eq {
                ty: self.subst(ty, map)?,
                left: self.subst(left, map)?,
                right: self.subst(right, map)?,
            },
            Term::Refl { ty, value } => Term::Refl {
                ty: self.subst(ty, map)?,
                value: self.subst(value, map)?,
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
                ty: self.subst(ty, map)?,
                left: self.subst(left, map)?,
                motive: self.subst(motive, map)?,
                base: self.subst(base, map)?,
                right: self.subst(right, map)?,
                proof: self.subst(proof, map)?,
            },
            Term::Vec { ty, len } => Term::Vec {
                ty: self.subst(ty, map)?,
                len: self.subst(len, map)?,
            },
            Term::VNil { ty } => Term::VNil {
                ty: self.subst(ty, map)?,
            },
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => Term::VCons {
                ty: self.subst(ty, map)?,
                len: self.subst(len, map)?,
                head: self.subst(head, map)?,
                tail: self.subst(tail, map)?,
            },
            Term::Fin { bound } => Term::Fin {
                bound: self.subst(bound, map)?,
            },
            Term::FZ { bound } => Term::FZ {
                bound: self.subst(bound, map)?,
            },
            Term::FS { bound, pred } => Term::FS {
                bound: self.subst(bound, map)?,
                pred: self.subst(pred, map)?,
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
                ty: self.subst(ty, map)?,
                motive: self.subst(motive, map)?,
                nil: self.subst(nil, map)?,
                cons: self.subst(cons, map)?,
                len: self.subst(len, map)?,
                scrutinee: self.subst(scrutinee, map)?,
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
                motive: self.subst(motive, map)?,
                zero: self.subst(zero, map)?,
                step: self.subst(step, map)?,
                bound: self.subst(bound, map)?,
                scrutinee: self.subst(scrutinee, map)?,
            },
            Term::Fin0Elim { ty, absurd } => Term::Fin0Elim {
                ty: self.subst(ty, map)?,
                absurd: self.subst(absurd, map)?,
            },
            Term::Succ(n) => Term::Succ(self.subst(n, map)?),
            Term::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => Term::NatElim {
                level: *level,
                motive: self.subst(motive, map)?,
                zero: self.subst(zero, map)?,
                step: self.subst(step, map)?,
                scrutinee: self.subst(scrutinee, map)?,
            },
            Term::App(f, x) => Term::App(self.subst(f, map)?, self.subst(x, map)?),
            Term::Meta(id, args) => Term::Meta(
                *id,
                args.iter()
                    .map(|x| self.subst(x, map))
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
                let domain = self.subst(domain, map)?;
                let new_id = self.fresh();
                let mut map = map.clone();
                map.insert(*id, Term::Local(new_id).arc());
                let body = self.subst(body, &map)?;
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
        .arc())
    }
    fn replace(&mut self, term: &T, id: Id, arg: T) -> Result<T, Error> {
        self.subst(term, &HashMap::from([(id, arg)]))
    }

    fn whnf(&mut self, term: &T) -> Result<T, Error> {
        self.tick()?;
        match term.as_ref() {
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

    fn zonk(&mut self, term: &T) -> Result<T, Error> {
        let term = self.whnf(term)?;
        Ok(match term.as_ref() {
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
            Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => return Ok(term),
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
    fn expand(&mut self, term: &T) -> Result<T, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
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
            Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => return Ok(term.clone()),
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

    pub fn type_expr(&mut self, ctx: &Context, expr: &Expr) -> Result<(T, u32), Error> {
        let (term, ty) = self.synth(ctx, expr)?;
        match self.whnf(&ty)?.as_ref() {
            Term::Universe(level) => Ok((term, *level)),
            _ => Err(Error::ExpectedUniverse),
        }
    }

    pub fn synth(&mut self, ctx: &Context, expr: &Expr) -> Result<(T, T), Error> {
        self.tick()?;
        match expr {
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
                let local = ctx
                    .iter()
                    .rev()
                    .find(|x| x.name == *name)
                    .ok_or_else(|| Error::UnknownName(name.clone()))?;
                Ok((Term::Local(local.id).arc(), local.ty.clone()))
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
            Expr::Hole => Err(Error::AnnotationRequired),
        }
    }

    pub fn check(&mut self, ctx: &Context, expr: &Expr, expected: &T) -> Result<T, Error> {
        self.tick()?;
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
        self.unify(&ty, expected)?;
        Ok(term)
    }

    fn unify(&mut self, a: &T, b: &T) -> Result<(), Error> {
        self.tick()?;
        let a = self.whnf(a)?;
        let b = self.whnf(b)?;
        if a == b {
            return Ok(());
        }
        match (a.as_ref(), b.as_ref()) {
            (
                Term::Sigma { id, domain, body },
                Term::Sigma {
                    id: id2,
                    domain: d2,
                    body: b2,
                },
            ) => {
                self.unify(domain, d2)?;
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                let b2 = self.replace(b2, *id2, x)?;
                self.unify(&body, &b2)
            }
            (
                Term::Pair { ty, fst, snd },
                Term::Pair {
                    ty: t2,
                    fst: f2,
                    snd: s2,
                },
            ) => {
                self.unify(ty, t2)?;
                self.unify(fst, f2)?;
                self.unify(snd, s2)
            }
            (Term::Fst(a), Term::Fst(b)) | (Term::Snd(a), Term::Snd(b)) => self.unify(a, b),
            (
                Term::Inductive { id, parameters },
                Term::Inductive {
                    id: id2,
                    parameters: parameters2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (
                Term::Constructor {
                    id,
                    parameters,
                    fields,
                },
                Term::Constructor {
                    id: id2,
                    parameters: parameters2,
                    fields: fields2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                if fields.len() != fields2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in fields.iter().zip(fields2) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (
                Term::Elim {
                    id,
                    parameters,
                    level,
                    motive,
                    branch,
                    scrutinee,
                },
                Term::Elim {
                    id: id2,
                    parameters: parameters2,
                    level: level2,
                    motive: motive2,
                    branch: branch2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(motive, motive2)?;
                self.unify(branch, branch2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (Term::Meta(id, args), _) => self.solve(*id, args, &b),
            (_, Term::Meta(id, args)) => self.solve(*id, args, &a),
            (
                Term::Pi {
                    id,
                    plicity,
                    domain,
                    body,
                },
                Term::Pi {
                    id: id2,
                    plicity: p2,
                    domain: d2,
                    body: b2,
                },
            )
            | (
                Term::Lam {
                    id,
                    plicity,
                    domain,
                    body,
                },
                Term::Lam {
                    id: id2,
                    plicity: p2,
                    domain: d2,
                    body: b2,
                },
            ) => {
                if plicity != p2 {
                    return Err(Error::PlicityMismatch);
                }
                self.unify(domain, d2)?;
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                let b2 = self.replace(b2, *id2, x)?;
                self.unify(&body, &b2)
            }
            (
                Term::Eq { ty, left, right },
                Term::Eq {
                    ty: ty2,
                    left: left2,
                    right: right2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(left, left2)?;
                self.unify(right, right2)?;
                Ok(())
            }
            (
                Term::Refl { ty, value },
                Term::Refl {
                    ty: ty2,
                    value: value2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(value, value2)?;
                Ok(())
            }
            (
                Term::J {
                    level,
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                },
                Term::J {
                    level: level2,
                    ty: ty2,
                    left: left2,
                    motive: motive2,
                    base: base2,
                    right: right2,
                    proof: proof2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(ty, ty2)?;
                self.unify(left, left2)?;
                self.unify(motive, motive2)?;
                self.unify(base, base2)?;
                self.unify(right, right2)?;
                self.unify(proof, proof2)?;
                Ok(())
            }
            (Term::Vec { ty, len }, Term::Vec { ty: ty2, len: len2 }) => {
                self.unify(ty, ty2)?;
                self.unify(len, len2)?;
                Ok(())
            }
            (Term::VNil { ty }, Term::VNil { ty: ty2 }) => {
                self.unify(ty, ty2)?;
                Ok(())
            }
            (
                Term::VCons {
                    ty,
                    len,
                    head,
                    tail,
                },
                Term::VCons {
                    ty: ty2,
                    len: len2,
                    head: head2,
                    tail: tail2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(len, len2)?;
                self.unify(head, head2)?;
                self.unify(tail, tail2)?;
                Ok(())
            }
            (Term::Fin { bound }, Term::Fin { bound: bound2 }) => {
                self.unify(bound, bound2)?;
                Ok(())
            }
            (Term::FZ { bound }, Term::FZ { bound: bound2 }) => {
                self.unify(bound, bound2)?;
                Ok(())
            }
            (
                Term::FS { bound, pred },
                Term::FS {
                    bound: bound2,
                    pred: pred2,
                },
            ) => {
                self.unify(bound, bound2)?;
                self.unify(pred, pred2)?;
                Ok(())
            }
            (
                Term::VecElim {
                    level,
                    ty,
                    motive,
                    nil,
                    cons,
                    len,
                    scrutinee,
                },
                Term::VecElim {
                    level: level2,
                    ty: ty2,
                    motive: motive2,
                    nil: nil2,
                    cons: cons2,
                    len: len2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(ty, ty2)?;
                self.unify(motive, motive2)?;
                self.unify(nil, nil2)?;
                self.unify(cons, cons2)?;
                self.unify(len, len2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (
                Term::FinElim {
                    level,
                    motive,
                    zero,
                    step,
                    bound,
                    scrutinee,
                },
                Term::FinElim {
                    level: level2,
                    motive: motive2,
                    zero: zero2,
                    step: step2,
                    bound: bound2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(motive, motive2)?;
                self.unify(zero, zero2)?;
                self.unify(step, step2)?;
                self.unify(bound, bound2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (
                Term::Fin0Elim { ty, absurd },
                Term::Fin0Elim {
                    ty: ty2,
                    absurd: absurd2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(absurd, absurd2)?;
                Ok(())
            }
            (Term::Succ(x), Term::Succ(y)) => self.unify(x, y),
            (
                Term::NatElim {
                    level: l,
                    motive: p,
                    zero: z,
                    step: s,
                    scrutinee: n,
                },
                Term::NatElim {
                    level: l2,
                    motive: p2,
                    zero: z2,
                    step: s2,
                    scrutinee: n2,
                },
            ) => {
                if l != l2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(p, p2)?;
                self.unify(z, z2)?;
                self.unify(s, s2)?;
                self.unify(n, n2)
            }
            (Term::App(f, x), Term::App(g, y)) => {
                self.unify(f, g)?;
                self.unify(x, y)
            }
            // Eta only for lambda versus a neutral term. No general search.
            (
                Term::Lam { id, body, .. },
                Term::Local(_)
                | Term::App(_, _)
                | Term::NatElim { .. }
                | Term::J { .. }
                | Term::VecElim { .. }
                | Term::FinElim { .. }
                | Term::Fst(_)
                | Term::Snd(_)
                | Term::Elim { .. }
                | Term::Fin0Elim { .. },
            ) => {
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                self.unify(&body, &Term::App(b.clone(), x).arc())
            }
            (
                Term::Local(_)
                | Term::App(_, _)
                | Term::NatElim { .. }
                | Term::J { .. }
                | Term::VecElim { .. }
                | Term::FinElim { .. }
                | Term::Fst(_)
                | Term::Snd(_)
                | Term::Elim { .. }
                | Term::Fin0Elim { .. },
                Term::Lam { .. },
            ) => self.unify(&b, &a),
            _ => Err(Error::CannotUnify),
        }
    }

    fn solve(&mut self, id: Id, args: &[T], rhs: &T) -> Result<(), Error> {
        // Only contextual pattern spines, with distinct variables, are solved.
        let telescope = self.metas[id].telescope.clone();
        let mut rename = HashMap::new();
        for (arg, local) in args.iter().zip(&telescope) {
            let arg = self.whnf(arg)?;
            let Term::Local(arg_id) = arg.as_ref() else {
                return Err(Error::NonPattern);
            };
            if rename
                .insert(*arg_id, Term::Local(local.id).arc())
                .is_some()
            {
                return Err(Error::NonPattern);
            }
        }
        let rhs = self.zonk(rhs)?;
        self.validate_solution(id, &rhs, &mut rename.keys().copied().collect())?;
        let solution = self.subst(&rhs, &rename)?;
        self.metas[id].solution = Some(solution);
        Ok(())
    }

    fn validate_solution(
        &mut self,
        solving: Id,
        term: &T,
        allowed: &mut HashSet<Id>,
    ) -> Result<(), Error> {
        self.tick()?;
        match term.as_ref() {
            Term::Inductive { parameters, .. } => {
                for child in parameters {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Constructor {
                parameters, fields, ..
            } => {
                for child in parameters.iter().chain(fields) {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Elim {
                parameters,
                motive,
                branch,
                scrutinee,
                ..
            } => {
                for child in parameters.iter().chain([motive, branch, scrutinee]) {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fst(p) | Term::Snd(p) => self.validate_solution(solving, p, allowed),
            Term::Pair { ty, fst, snd } => {
                for child in [ty, fst, snd] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Local(id) if !allowed.contains(id) => Err(Error::ScopeEscape),
            Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => Ok(()),
            Term::Eq {
                ty, left, right, ..
            } => {
                for child in [ty, left, right] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Refl { ty, value, .. } => {
                for child in [ty, value] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::J {
                ty,
                left,
                motive,
                base,
                right,
                proof,
                ..
            } => {
                for child in [ty, left, motive, base, right, proof] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Vec { ty, len, .. } => {
                for child in [ty, len] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::VNil { ty, .. } => {
                self.validate_solution(solving, ty, allowed)?;
                Ok(())
            }
            Term::VCons {
                ty,
                len,
                head,
                tail,
                ..
            } => {
                for child in [ty, len, head, tail] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fin { bound, .. } => {
                self.validate_solution(solving, bound, allowed)?;
                Ok(())
            }
            Term::FZ { bound, .. } => {
                self.validate_solution(solving, bound, allowed)?;
                Ok(())
            }
            Term::FS { bound, pred, .. } => {
                for child in [bound, pred] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::VecElim {
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
                ..
            } => {
                for child in [ty, motive, nil, cons, len, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::FinElim {
                motive,
                zero,
                step,
                bound,
                scrutinee,
                ..
            } => {
                for child in [motive, zero, step, bound, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fin0Elim { ty, absurd, .. } => {
                for child in [ty, absurd] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Succ(n) => self.validate_solution(solving, n, allowed),
            Term::NatElim {
                motive,
                zero,
                step,
                scrutinee,
                ..
            } => {
                for child in [motive, zero, step, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Meta(id, _) if *id == solving => Err(Error::OccursCheck),
            Term::Meta(_, args) => {
                for arg in args {
                    self.validate_solution(solving, arg, allowed)?;
                }
                Ok(())
            }
            Term::App(f, x) => {
                self.validate_solution(solving, f, allowed)?;
                self.validate_solution(solving, x, allowed)
            }
            Term::Sigma { id, domain, body }
            | Term::Pi {
                id, domain, body, ..
            }
            | Term::Lam {
                id, domain, body, ..
            } => {
                self.validate_solution(solving, domain, allowed)?;
                let inserted = allowed.insert(*id);
                let result = self.validate_solution(solving, body, allowed);
                if inserted {
                    allowed.remove(id);
                }
                result
            }
        }
    }

    fn core(&mut self, term: &T, scope: &mut Vec<Id>) -> Result<Tm, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
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

    fn import_core(&mut self, term: &Tm, scope: &mut Vec<Id>) -> Result<T, Error> {
        self.tick()?;
        Ok(match term.as_ref() {
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
    pub fn finish(&mut self, term: T, ty: T, kernel: &Kernel) -> Result<Elaborated, Error> {
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

fn pi(id: Id, domain: T, body: T) -> T {
    Term::Pi {
        id,
        plicity: Plicity::Explicit,
        domain,
        body,
    }
    .arc()
}
fn app2(f: T, a: T, b: T) -> T {
    Term::App(Term::App(f, a).arc(), b).arc()
}

#[cfg(test)]
mod tests {
    use super::*;
    fn u(n: u32) -> T {
        Term::Universe(n).arc()
    }
    fn local(id: Id) -> T {
        Term::Local(id).arc()
    }

    fn inductive_children(child: T) -> Vec<T> {
        let n = Term::Nat.arc();
        vec![
            Term::Inductive {
                id: 1,
                parameters: vec![child.clone()],
            }
            .arc(),
            Term::Constructor {
                id: 1,
                parameters: vec![child.clone()],
                fields: vec![],
            }
            .arc(),
            Term::Constructor {
                id: 1,
                parameters: vec![],
                fields: vec![child.clone()],
            }
            .arc(),
            Term::Elim {
                id: 1,
                parameters: vec![child.clone()],
                level: 0,
                motive: n.clone(),
                branch: n.clone(),
                scrutinee: n.clone(),
            }
            .arc(),
            Term::Elim {
                id: 1,
                parameters: vec![],
                level: 0,
                motive: child.clone(),
                branch: n.clone(),
                scrutinee: n.clone(),
            }
            .arc(),
            Term::Elim {
                id: 1,
                parameters: vec![],
                level: 0,
                motive: n.clone(),
                branch: child.clone(),
                scrutinee: n.clone(),
            }
            .arc(),
            Term::Elim {
                id: 1,
                parameters: vec![],
                level: 0,
                motive: n.clone(),
                branch: n.clone(),
                scrutinee: child,
            }
            .arc(),
        ]
    }
    #[test]
    fn inductive_children_enforce_occurs_scope_and_substitution() {
        let mut s = State::new(100_000);
        let m = s.meta(&vec![], u(0));
        for term in inductive_children(m) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::new()),
                Err(Error::OccursCheck)
            );
        }
        for term in inductive_children(local(100)) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::new()),
                Err(Error::ScopeEscape)
            );
            let closed = s
                .subst(&term, &HashMap::from([(100, Term::Nat.arc())]))
                .unwrap();
            s.validate_solution(0, &closed, &mut HashSet::new())
                .unwrap();
        }
    }
    #[test]
    fn kernel_rechecks_embedded_constructor_before_elimination() {
        let mut k = Kernel::default();
        k.declare(
            1,
            deppy_core::InductiveDecl {
                parameters: vec![],
                fields: vec![Core::Nat.arc()],
                level: 0,
            },
        )
        .unwrap();
        let mut s = State::with_kernel(100_000, k.clone());
        let motive = Term::Lam {
            id: 0,
            plicity: Plicity::Explicit,
            domain: Term::Inductive {
                id: 1,
                parameters: vec![],
            }
            .arc(),
            body: Term::Nat.arc(),
        }
        .arc();
        let branch = Term::Lam {
            id: 1,
            plicity: Plicity::Explicit,
            domain: Term::Nat.arc(),
            body: Term::Zero.arc(),
        }
        .arc();
        let bad = Term::Elim {
            id: 1,
            parameters: vec![],
            level: 0,
            motive,
            branch,
            scrutinee: Term::Constructor {
                id: 1,
                parameters: vec![],
                fields: vec![u(0)],
            }
            .arc(),
        }
        .arc();
        assert!(matches!(
            s.finish(bad, Term::Nat.arc(), &k),
            Err(Error::Kernel(_))
        ));
    }

    fn sigma_children(child: T) -> Vec<T> {
        let n = Term::Nat.arc();
        vec![
            Term::Sigma {
                id: 50,
                domain: child.clone(),
                body: n.clone(),
            }
            .arc(),
            Term::Sigma {
                id: 50,
                domain: n.clone(),
                body: child.clone(),
            }
            .arc(),
            Term::Pair {
                ty: child.clone(),
                fst: n.clone(),
                snd: n.clone(),
            }
            .arc(),
            Term::Pair {
                ty: n.clone(),
                fst: child.clone(),
                snd: n.clone(),
            }
            .arc(),
            Term::Pair {
                ty: n.clone(),
                fst: n.clone(),
                snd: child.clone(),
            }
            .arc(),
            Term::Fst(child.clone()).arc(),
            Term::Snd(child).arc(),
        ]
    }
    #[test]
    fn sigma_children_enforce_occurs_and_scope_checks() {
        let mut s = State::new(100_000);
        let m = s.meta(&vec![], u(0));
        for term in sigma_children(m) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::new()),
                Err(Error::OccursCheck)
            );
        }
        for term in sigma_children(local(100)) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::new()),
                Err(Error::ScopeEscape)
            );
        }
        let bound = Term::Sigma {
            id: 50,
            domain: u(0),
            body: local(50),
        }
        .arc();
        s.validate_solution(0, &bound, &mut HashSet::new()).unwrap();
        let substituted = s.subst(&bound, &HashMap::from([(50, local(100))])).unwrap();
        s.validate_solution(0, &substituted, &mut HashSet::new())
            .unwrap();
    }
    #[test]
    fn kernel_rechecks_pairs_before_projection_discards_components() {
        for first in [true, false] {
            let mut s = State::new(100_000);
            let ty = Term::Sigma {
                id: 0,
                domain: Term::Nat.arc(),
                body: Term::Nat.arc(),
            }
            .arc();
            let p = Term::Pair {
                ty,
                fst: if first { Term::Zero.arc() } else { u(0) },
                snd: if first { u(0) } else { Term::Zero.arc() },
            }
            .arc();
            let projection = if first { Term::Fst(p) } else { Term::Snd(p) }.arc();
            assert!(matches!(
                s.finish(projection, Term::Nat.arc(), &Kernel::default()),
                Err(Error::Kernel(_))
            ));
        }
    }

    fn indexed_children(child: T) -> Vec<T> {
        vec![
            Term::Vec {
                ty: child.clone(),
                len: local(0),
            }
            .arc(),
            Term::Vec {
                ty: local(0),
                len: child.clone(),
            }
            .arc(),
            Term::VNil { ty: child.clone() }.arc(),
            Term::VCons {
                ty: child.clone(),
                len: local(0),
                head: local(0),
                tail: local(0),
            }
            .arc(),
            Term::VCons {
                ty: local(0),
                len: child.clone(),
                head: local(0),
                tail: local(0),
            }
            .arc(),
            Term::VCons {
                ty: local(0),
                len: local(0),
                head: child.clone(),
                tail: local(0),
            }
            .arc(),
            Term::VCons {
                ty: local(0),
                len: local(0),
                head: local(0),
                tail: child.clone(),
            }
            .arc(),
            Term::Fin {
                bound: child.clone(),
            }
            .arc(),
            Term::FZ {
                bound: child.clone(),
            }
            .arc(),
            Term::FS {
                bound: child.clone(),
                pred: local(0),
            }
            .arc(),
            Term::FS {
                bound: local(0),
                pred: child.clone(),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: child.clone(),
                motive: local(0),
                nil: local(0),
                cons: local(0),
                len: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: local(0),
                motive: child.clone(),
                nil: local(0),
                cons: local(0),
                len: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: local(0),
                motive: local(0),
                nil: child.clone(),
                cons: local(0),
                len: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: local(0),
                motive: local(0),
                nil: local(0),
                cons: child.clone(),
                len: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: local(0),
                motive: local(0),
                nil: local(0),
                cons: local(0),
                len: child.clone(),
                scrutinee: local(0),
            }
            .arc(),
            Term::VecElim {
                level: 0,
                ty: local(0),
                motive: local(0),
                nil: local(0),
                cons: local(0),
                len: local(0),
                scrutinee: child.clone(),
            }
            .arc(),
            Term::FinElim {
                level: 0,
                motive: child.clone(),
                zero: local(0),
                step: local(0),
                bound: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::FinElim {
                level: 0,
                motive: local(0),
                zero: child.clone(),
                step: local(0),
                bound: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::FinElim {
                level: 0,
                motive: local(0),
                zero: local(0),
                step: child.clone(),
                bound: local(0),
                scrutinee: local(0),
            }
            .arc(),
            Term::FinElim {
                level: 0,
                motive: local(0),
                zero: local(0),
                step: local(0),
                bound: child.clone(),
                scrutinee: local(0),
            }
            .arc(),
            Term::FinElim {
                level: 0,
                motive: local(0),
                zero: local(0),
                step: local(0),
                bound: local(0),
                scrutinee: child.clone(),
            }
            .arc(),
            Term::Fin0Elim {
                ty: child.clone(),
                absurd: local(0),
            }
            .arc(),
            Term::Fin0Elim {
                ty: local(0),
                absurd: child.clone(),
            }
            .arc(),
        ]
    }
    #[test]
    fn indexed_children_enforce_occurs_and_scope_checks() {
        let mut s = State::new(100_000);
        let m = s.meta(&vec![], u(0));
        for term in indexed_children(m) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::from([0])),
                Err(Error::OccursCheck)
            );
        }
        for term in indexed_children(local(100)) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::from([0])),
                Err(Error::ScopeEscape)
            );
        }
    }
    #[test]
    fn kernel_rechecks_indexed_eliminators_before_discarding_branches() {
        let mut s = State::new(10_000);
        let bad_vec = Term::VecElim {
            level: 0,
            ty: Term::Nat.arc(),
            motive: Term::Nat.arc(),
            nil: Term::Zero.arc(),
            cons: Term::Zero.arc(),
            len: Term::Zero.arc(),
            scrutinee: Term::VNil {
                ty: Term::Nat.arc(),
            }
            .arc(),
        }
        .arc();
        assert!(matches!(
            s.finish(bad_vec, Term::Nat.arc(), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
        let id = s.fresh();
        let zero = Term::Lam {
            id,
            plicity: Plicity::Explicit,
            domain: Term::Nat.arc(),
            body: Term::Zero.arc(),
        }
        .arc();
        let bad_fin = Term::FinElim {
            level: 0,
            motive: Term::Nat.arc(),
            zero,
            step: Term::Zero.arc(),
            bound: Term::Succ(Term::Zero.arc()).arc(),
            scrutinee: Term::FZ {
                bound: Term::Zero.arc(),
            }
            .arc(),
        }
        .arc();
        assert!(matches!(
            s.finish(bad_fin, Term::Nat.arc(), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }
    fn equality_children(child: T) -> Vec<T> {
        let mut terms = vec![
            Term::Eq {
                ty: child.clone(),
                left: local(0),
                right: local(0),
            }
            .arc(),
            Term::Eq {
                ty: u(0),
                left: child.clone(),
                right: local(0),
            }
            .arc(),
            Term::Eq {
                ty: u(0),
                left: local(0),
                right: child.clone(),
            }
            .arc(),
            Term::Refl {
                ty: child.clone(),
                value: local(0),
            }
            .arc(),
            Term::Refl {
                ty: u(0),
                value: child.clone(),
            }
            .arc(),
        ];
        for index in 0..6 {
            let mut fields = [u(0), local(0), local(0), local(0), local(0), local(0)];
            fields[index] = child.clone();
            let [ty, left, motive, base, right, proof] = fields;
            terms.push(
                Term::J {
                    level: 0,
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                }
                .arc(),
            );
        }
        terms
    }
    #[test]
    fn equality_children_enforce_occurs_and_scope_checks() {
        let mut s = State::new(100_000);
        let m = s.meta(&vec![], u(0));
        for term in equality_children(m) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::from([0])),
                Err(Error::OccursCheck)
            );
        }
        for term in equality_children(local(100)) {
            assert_eq!(
                s.validate_solution(0, &term, &mut HashSet::from([0])),
                Err(Error::ScopeEscape)
            );
        }
    }
    #[test]
    fn kernel_sees_invalid_j_before_iota_reduction() {
        let mut s = State::new(10_000);
        let invalid = Term::J {
            level: 0,
            ty: Term::Nat.arc(),
            left: Term::Zero.arc(),
            motive: Term::Nat.arc(),
            base: Term::Zero.arc(),
            right: Term::Zero.arc(),
            proof: Term::Refl {
                ty: Term::Nat.arc(),
                value: Term::Zero.arc(),
            }
            .arc(),
        }
        .arc();
        assert!(matches!(
            s.finish(invalid, Term::Nat.arc(), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }

    #[test]
    fn rejects_direct_occurs_cycle() {
        let mut s = State::new(10_000);
        let m = s.meta(&vec![], u(1));
        let rhs = Term::App(m.clone(), u(0)).arc();
        assert_eq!(s.unify(&m, &rhs), Err(Error::OccursCheck));
    }
    #[test]
    fn rejects_indirect_occurs_cycle() {
        let mut s = State::new(10_000);
        let a = s.meta(&vec![], u(1));
        let b = s.meta(&vec![], u(1));
        s.unify(&a, &b).unwrap();
        assert_eq!(
            s.unify(&b, &Term::App(a, u(0)).arc()),
            Err(Error::OccursCheck)
        );
    }
    #[test]
    fn rejects_later_variable_escaping() {
        let mut s = State::new(10_000);
        let m = s.meta(&vec![], u(1));
        let later = local(s.fresh());
        assert_eq!(s.unify(&m, &later), Err(Error::ScopeEscape));
    }
    #[test]
    fn scope_check_looks_inside_other_meta_spines() {
        let mut s = State::new(10_000);
        let outer = s.meta(&vec![], u(1));
        let (ctx, _) = s.bind(&vec![], "later", u(1));
        let inner = s.meta(&ctx, u(1));
        assert_eq!(s.unify(&outer, &inner), Err(Error::ScopeEscape));
    }
    #[test]
    fn contextual_solution_is_renamed_at_each_occurrence() {
        let mut s = State::new(10_000);
        let (ctx, original) = s.bind(&vec![], "A", u(1));
        let m = s.meta(&ctx, u(1));
        let new = s.fresh();
        let occurrence = s.replace(&m, original, local(new)).unwrap();
        s.unify(&occurrence, &local(new)).unwrap();
        assert_eq!(s.whnf(&m).unwrap(), local(original));
        assert_eq!(s.whnf(&occurrence).unwrap(), local(new));
    }
    #[test]
    fn rejects_non_variable_and_repeated_spines() {
        let mut s = State::new(10_000);
        let (ctx, a) = s.bind(&vec![], "A", u(1));
        let (ctx, b) = s.bind(&ctx, "B", u(1));
        let m = s.meta(&ctx, u(1));
        let repeated = s.replace(&m, b, local(a)).unwrap();
        assert_eq!(s.unify(&repeated, &local(a)), Err(Error::NonPattern));
        let concrete = s.replace(&m, a, u(0)).unwrap();
        assert_eq!(s.unify(&concrete, &u(0)), Err(Error::NonPattern));
    }
    #[test]
    fn accepts_bound_variables_inside_solutions() {
        let mut s = State::new(10_000);
        let m = s.meta(&vec![], u(1));
        let id = s.fresh();
        let rhs = Term::Pi {
            id,
            plicity: Plicity::Explicit,
            domain: u(0),
            body: local(id),
        }
        .arc();
        s.unify(&m, &rhs).unwrap();
        s.finish(m, u(1), &Kernel::default()).unwrap();
    }
    #[test]
    fn expected_meta_type_is_rechecked_even_if_meta_is_unused() {
        let mut s = State::new(10_000);
        let m = s.meta(&vec![], u(0));
        s.unify(&m, &u(0)).unwrap(); // This candidate has the wrong universe.
        assert!(matches!(
            s.finish(u(0), u(1), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }
    #[test]
    fn kernel_sees_invalid_subterms_before_beta_reduction() {
        let mut s = State::new(10_000);
        let id = s.fresh();
        let invalid = Term::App(
            Term::Lam {
                id,
                plicity: Plicity::Explicit,
                domain: u(0),
                body: u(0),
            }
            .arc(),
            u(0),
        )
        .arc();
        // Beta reduction would hide the ill-typed argument Type0 : Type0.
        assert!(matches!(
            s.finish(invalid, u(1), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }
    #[test]
    fn kernel_rechecks_final_claimed_type() {
        let mut s = State::new(10_000);
        assert!(matches!(
            s.finish(u(0), u(0), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }
    #[test]
    fn substitution_avoids_capture() {
        let mut s = State::new(10_000);
        let a = s.fresh();
        let b = s.fresh();
        let term = Term::Lam {
            id: b,
            plicity: Plicity::Explicit,
            domain: u(0),
            body: local(a),
        }
        .arc();
        let result = s.replace(&term, a, local(b)).unwrap();
        let Term::Lam { id, body, .. } = result.as_ref() else {
            panic!()
        };
        assert_ne!(*id, b);
        assert_eq!(body, &local(b));
    }
}
