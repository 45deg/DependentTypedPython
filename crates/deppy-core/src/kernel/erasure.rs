//! Type-directed erasure of independently checked core terms.
use super::*;
use crate::Relevance;

/// Pure runtime IR. Variable indices count retained binders only.
/// Types and reflexivity payloads have no runtime representation; equality
/// elimination retains a proof token rather than assuming arbitrary transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeTerm {
    Unit,
    Record(crate::InductiveId, Vec<Self>),
    RecordElim(crate::InductiveId, Box<Self>, Box<Self>),
    Var(usize),
    Global(crate::DefId),
    Lam(Box<Self>),
    App(Box<Self>, Box<Self>),
    Let(Box<Self>, Box<Self>),
    Prim(&'static str, Vec<Self>),
}
impl Kernel {
    /// Kernel validation precedes usage checking, including discarded subterms.
    pub fn erase(&self, term: &Tm) -> Result<RuntimeTerm, Error> {
        self.infer(term)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone());
        erase(&self.context(), term, &[], &mut budget)
    }

    /// Include private helpers as well as public definitions. Definitions cannot
    /// refer forwards, so successful traversal checks every runtime dependency.
    pub fn erase_definitions(&self) -> Result<Vec<(crate::DefId, RuntimeTerm)>, Error> {
        self.definitions
            .iter()
            .map(|(id, d)| Ok((*id, self.erase(&d.body)?)))
            .collect()
    }
}
fn erase(
    ctx: &Context,
    term: &Tm,
    kept: &[bool],
    budget: &mut Budget,
) -> Result<RuntimeTerm, Error> {
    budget.tick()?;
    if matches!(synth(ctx, term, budget)?.as_ref(), Value::Universe(_)) {
        return Ok(RuntimeTerm::Unit);
    }
    let mut sub = |t: &Tm| erase(ctx, t, kept, budget);
    let prim = |name, args| Ok(RuntimeTerm::Prim(name, args));
    match term.as_ref() {
        Term::Var(i) => {
            let pos = kept
                .len()
                .checked_sub(i + 1)
                .ok_or(Error::UnboundVariable(*i))?;
            if !kept[pos] {
                return Err(Error::ErasedVariableUsed(*i));
            }
            Ok(RuntimeTerm::Var(
                kept[pos + 1..].iter().filter(|x| **x).count(),
            ))
        }
        Term::Global(id) => Ok(RuntimeTerm::Global(*id)),
        Term::Lam {
            relevance,
            domain,
            body,
        } => {
            let domain = value::eval(domain, &ctx.env, budget)?;
            let retain = *relevance == Relevance::Runtime;
            let mut next = kept.to_vec();
            next.push(retain);
            let body = erase(&ctx.bind(domain), body, &next, budget)?;
            Ok(if retain {
                RuntimeTerm::Lam(Box::new(body))
            } else {
                body
            })
        }
        Term::App { function, argument } => {
            let ty = synth(ctx, function, budget)?;
            let Value::Pi(relevance, _, _) = ty.as_ref() else {
                return Err(Error::ExpectedFunction);
            };
            let f = erase(ctx, function, kept, budget)?;
            if *relevance == Relevance::Erased {
                Ok(f)
            } else {
                Ok(RuntimeTerm::App(
                    Box::new(f),
                    Box::new(erase(ctx, argument, kept, budget)?),
                ))
            }
        }
        Term::Let { ty, value: v, body } => {
            let rhs = sub(v)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            let val = value::eval(v, &ctx.env, budget)?;
            let mut next = kept.to_vec();
            next.push(true);
            Ok(RuntimeTerm::Let(
                Box::new(rhs),
                Box::new(erase(&ctx.define(ty, val), body, &next, budget)?),
            ))
        }
        Term::Zero => prim("zero", vec![]),
        Term::Succ(n) => prim("succ", vec![sub(n)?]),
        Term::NatElim {
            zero,
            step,
            scrutinee,
            ..
        } => prim("nat_elim", vec![sub(zero)?, sub(step)?, sub(scrutinee)?]),
        Term::VNil { .. } => prim("vnil", vec![]),
        Term::VCons {
            len, head, tail, ..
        } => prim("vcons", vec![sub(len)?, sub(head)?, sub(tail)?]),
        Term::VecElim {
            nil,
            cons,
            scrutinee,
            ..
        } => prim("vec_elim", vec![sub(nil)?, sub(cons)?, sub(scrutinee)?]),
        Term::FZ { bound } => prim("fz", vec![sub(bound)?]),
        Term::FS { bound, pred } => prim("fs", vec![sub(bound)?, sub(pred)?]),
        Term::FinElim {
            zero,
            step,
            scrutinee,
            ..
        } => prim("fin_elim", vec![sub(zero)?, sub(step)?, sub(scrutinee)?]),
        Term::Fin0Elim { absurd, .. } => prim("absurd", vec![sub(absurd)?]),
        Term::Pair { fst, snd, .. } => prim("pair", vec![sub(fst)?, sub(snd)?]),
        Term::Fst(p) => prim("fst", vec![sub(p)?]),
        Term::Snd(p) => prim("snd", vec![sub(p)?]),
        Term::Constructor { id, fields, .. } => {
            let mut args = vec![];
            for f in fields {
                args.push(sub(f)?);
            }
            // Nominality is preserved in the runtime constructor tag.
            Ok(RuntimeTerm::Record(*id, args))
        }
        Term::Elim {
            id,
            branch,
            scrutinee,
            ..
        } => Ok(RuntimeTerm::RecordElim(
            *id,
            Box::new(sub(branch)?),
            Box::new(sub(scrutinee)?),
        )),
        Term::Refl { .. } => prim("refl", vec![]),
        Term::J { base, proof, .. } => prim("j", vec![sub(base)?, sub(proof)?]),
        Term::Universe(_)
        | Term::Pi { .. }
        | Term::Sigma { .. }
        | Term::Eq { .. }
        | Term::Nat
        | Term::Vec { .. }
        | Term::Fin { .. }
        | Term::Inductive { .. } => Ok(RuntimeTerm::Unit),
    }
}
