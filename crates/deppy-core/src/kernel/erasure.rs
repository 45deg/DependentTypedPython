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
            .filter_map(|(id, d)| d.body.as_ref().map(|body| Ok((*id, self.erase(body)?))))
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
        Term::Global(id) => {
            let body = budget
                .1
                .get(id)
                .ok_or(Error::UnknownDefinition(*id))?
                .body
                .clone()
                .ok_or(Error::AxiomHasNoRuntimeValue(*id))?;
            let closed = Context {
                globals: ctx.globals.clone(),
                ..Context::default()
            };
            erase(&closed, &body, &[], budget)?;
            Ok(RuntimeTerm::Global(*id))
        }
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

/// Runtime boundary schemas. Dependent sizes are checked using retained values.
/// Unknown type parameters accept only canonical immutable opaque data. Higher
/// order boundaries and sizes requiring erased indices are deliberately rejected.
#[derive(Clone, Debug)]
pub enum RuntimeType {
    Opaque,
    Type,
    Nat,
    Proof,
    Vec(Box<Self>, RuntimeTerm),
    Fin(RuntimeTerm),
    Pair(Box<Self>, Box<Self>),
    Record(crate::InductiveId, Vec<Self>),
}
#[derive(Clone, Debug)]
pub struct RuntimeSignature {
    pub arguments: Vec<RuntimeType>,
    pub result: RuntimeType,
}
impl Kernel {
    pub fn runtime_signature(&self, term: &Tm) -> Result<RuntimeSignature, Error> {
        self.infer(term)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone());
        let mut ctx = self.context();
        let mut ty = synth(&ctx, term, &mut budget)?;
        let mut kept = vec![];
        let mut arguments = vec![];
        while let Value::Pi(relevance, domain, codomain) = ty.as_ref() {
            let retain = *relevance == Relevance::Runtime;
            if retain {
                arguments.push(schema(&ctx, domain, &kept, &mut budget)?);
            }
            let next = codomain.apply(value::fresh(ctx.env.len()), &mut budget)?;
            ctx = ctx.bind(domain.clone());
            kept.push(retain);
            ty = next;
        }
        Ok(RuntimeSignature {
            arguments,
            result: schema(&ctx, &ty, &kept, &mut budget)?,
        })
    }
}
fn schema(
    ctx: &Context,
    ty: &Val,
    kept: &[bool],
    budget: &mut Budget,
) -> Result<RuntimeType, Error> {
    budget.tick()?;
    let mut index = |v| {
        let term = value::quote(v, ctx.env.len(), budget)?;
        erase(ctx, &term, kept, budget)
    };
    Ok(match ty.as_ref() {
        Value::Universe(_) => RuntimeType::Type,
        Value::Nat => RuntimeType::Nat,
        Value::Eq(..) => RuntimeType::Proof,
        Value::Vec { ty, len } => {
            let len = index(len)?;
            RuntimeType::Vec(Box::new(schema(ctx, ty, kept, budget)?), len)
        }
        Value::Fin { bound } => RuntimeType::Fin(index(bound)?),
        Value::Sigma(domain, codomain) => {
            let fst = schema(ctx, domain, kept, budget)?;
            let next_ty = codomain.apply(value::fresh(ctx.env.len()), budget)?;
            let mut next_kept = kept.to_vec();
            next_kept.push(true);
            let snd = schema(&ctx.bind(domain.clone()), &next_ty, &next_kept, budget)?;
            RuntimeType::Pair(Box::new(fst), Box::new(snd))
        }
        Value::Inductive { id, parameters } => {
            let decl = ctx.globals.get(id).ok_or(Error::UnknownInductive(*id))?;
            let mut env = parameters.clone();
            let mut field_ctx = ctx.clone();
            let mut field_kept = kept.to_vec();
            let mut fields = vec![];
            for field in &decl.fields {
                let ty = value::eval(field, &env, budget)?;
                fields.push(schema(&field_ctx, &ty, &field_kept, budget)?);
                env.push(value::fresh(field_ctx.env.len()));
                field_ctx = field_ctx.bind(ty);
                field_kept.push(true);
            }
            RuntimeType::Record(*id, fields)
        }
        // A bare type parameter is opaque. An arbitrary neutral type family may
        // change representation; silently treating it as opaque would be unsafe.
        Value::Neutral(value::Neutral::Var(_)) => RuntimeType::Opaque,
        _ => return Err(Error::UnsupportedRuntimeBoundary),
    })
}
