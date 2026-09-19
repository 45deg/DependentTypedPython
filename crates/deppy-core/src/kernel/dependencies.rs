use super::*;
use std::collections::BTreeSet;

impl Kernel {
    /// All explicit assumptions used by a checked term, including its type,
    /// annotations, referenced definitions and nominal record declarations.
    /// This is syntactic dependency tracking, not proof minimization.
    pub fn axiom_dependencies(&self, term: &Tm) -> Result<BTreeSet<crate::DefId>, Error> {
        let ty = self.infer(term)?;
        let mut pending = vec![term.clone(), ty];
        let mut definitions = BTreeSet::new();
        let mut records = BTreeSet::new();
        let mut axioms = BTreeSet::new();
        let mut remaining = self.max_steps;
        while let Some(term) = pending.pop() {
            remaining = remaining.checked_sub(1).ok_or(Error::BudgetExceeded)?;
            match term.as_ref() {
                Term::Global(id) => {
                    if definitions.insert(*id) {
                        let declaration = self.definition(*id)?;
                        pending.push(declaration.ty.clone());
                        if let Some(body) = &declaration.body {
                            pending.push(body.clone());
                        } else {
                            axioms.insert(*id);
                        }
                    }
                }
                Term::Inductive { id, parameters }
                | Term::Constructor { id, parameters, .. }
                | Term::Elim { id, parameters, .. } => {
                    pending.extend(parameters.iter().cloned());
                    if records.insert(*id) {
                        let declaration = self.declaration(*id)?;
                        pending.extend(declaration.parameters.iter().cloned());
                        pending.extend(declaration.fields.iter().cloned());
                    }
                    match term.as_ref() {
                        Term::Constructor { fields, .. } => pending.extend(fields.iter().cloned()),
                        Term::Elim {
                            motive,
                            branch,
                            scrutinee,
                            ..
                        } => pending.extend([motive.clone(), branch.clone(), scrutinee.clone()]),
                        _ => {}
                    }
                }
                Term::Sigma { domain, codomain }
                | Term::Pi {
                    domain, codomain, ..
                } => pending.extend([domain.clone(), codomain.clone()]),
                Term::Lam { domain, body, .. } => pending.extend([domain.clone(), body.clone()]),
                Term::Pair { ty, fst, snd } => {
                    pending.extend([ty.clone(), fst.clone(), snd.clone()])
                }
                Term::Fst(t) | Term::Snd(t) | Term::Succ(t) => pending.push(t.clone()),
                Term::Eq { ty, left, right } => {
                    pending.extend([ty.clone(), left.clone(), right.clone()])
                }
                Term::Refl { ty, value } => pending.extend([ty.clone(), value.clone()]),
                Term::J {
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                    ..
                } => pending.extend([
                    ty.clone(),
                    left.clone(),
                    motive.clone(),
                    base.clone(),
                    right.clone(),
                    proof.clone(),
                ]),
                Term::Vec { ty, len } => pending.extend([ty.clone(), len.clone()]),
                Term::VNil { ty } => pending.push(ty.clone()),
                Term::VCons {
                    ty,
                    len,
                    head,
                    tail,
                } => pending.extend([ty.clone(), len.clone(), head.clone(), tail.clone()]),
                Term::Fin { bound } | Term::FZ { bound } => pending.push(bound.clone()),
                Term::FS { bound, pred } => pending.extend([bound.clone(), pred.clone()]),
                Term::VecElim {
                    ty,
                    motive,
                    nil,
                    cons,
                    len,
                    scrutinee,
                    ..
                } => pending.extend([
                    ty.clone(),
                    motive.clone(),
                    nil.clone(),
                    cons.clone(),
                    len.clone(),
                    scrutinee.clone(),
                ]),
                Term::FinElim {
                    motive,
                    zero,
                    step,
                    bound,
                    scrutinee,
                    ..
                } => pending.extend([
                    motive.clone(),
                    zero.clone(),
                    step.clone(),
                    bound.clone(),
                    scrutinee.clone(),
                ]),
                Term::Fin0Elim { ty, absurd } => pending.extend([ty.clone(), absurd.clone()]),
                Term::NatElim {
                    motive,
                    zero,
                    step,
                    scrutinee,
                    ..
                } => pending.extend([
                    motive.clone(),
                    zero.clone(),
                    step.clone(),
                    scrutinee.clone(),
                ]),
                Term::App { function, argument } => {
                    pending.extend([function.clone(), argument.clone()])
                }
                Term::Let { ty, value, body } => {
                    pending.extend([ty.clone(), value.clone(), body.clone()])
                }
                Term::Var(_) | Term::Universe(_) | Term::Nat | Term::Zero => {}
            }
        }
        Ok(axioms)
    }
}
