//! Type-directed erasure of independently checked core terms.
use super::*;
use crate::Relevance;

/// Pure runtime IR. Variable indices count retained binders only.
/// Types and reflexivity payloads have no runtime representation. Discarded
/// proof results have a distinct marker that computational J cannot consume.
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
// Values stored in lets, passed to functions or constructors, or supplied to
// eliminators must remain usable by a later J, even behind a type variable or a
// higher-order function. Only a result position may discard its proof. This is
// deliberately conservative; it does not infer argument/field irrelevance.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProofDemand {
    Result,
    Computational,
}

impl Kernel {
    /// Kernel validation precedes usage checking, including discarded subterms.
    pub fn erase(&self, term: &Tm) -> Result<RuntimeTerm, Error> {
        self.infer(term)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        erase(&self.context(), term, &[], &mut budget, ProofDemand::Result)
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
    demand: ProofDemand,
) -> Result<RuntimeTerm, Error> {
    budget.tick()?;
    let ty = synth(ctx, term, budget)?;
    if matches!(ty.as_ref(), Value::Universe(_)) {
        return Ok(RuntimeTerm::Unit);
    }
    // A checked proof result can be discarded. The token is only an output
    // marker, never evidence for a computational J: all retained inputs below
    // are erased in computational mode, including higher-order arguments.
    if demand == ProofDemand::Result && matches!(ty.as_ref(), Value::Eq(..)) {
        return Ok(RuntimeTerm::Prim("erased_proof", vec![]));
    }
    let mut sub = |t: &Tm| erase(ctx, t, kept, budget, ProofDemand::Computational);
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
            let erased = erase(&closed, &body, &[], budget, demand)?;
            // The ordinary global may have discarded its proof result. Inline
            // the checked body for computational uses instead of reusing that
            // output marker. Definitions are acyclic; the budget bounds growth.
            Ok(if demand == ProofDemand::Computational {
                erased
            } else {
                RuntimeTerm::Global(*id)
            })
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
            let body = erase(&ctx.bind(domain), body, &next, budget, demand)?;
            Ok(if retain {
                RuntimeTerm::Lam(Box::new(body))
            } else {
                body
            })
        }
        Term::App { function, argument } => {
            // The elaborator represents source lets as immediate lambda
            // applications. Apply the same proof-usage rule to this encoding.
            if let Term::Lam {
                relevance: Relevance::Runtime,
                domain,
                body,
            } = function.as_ref()
            {
                if matches!(
                    value::eval(domain, &ctx.env, budget)?.as_ref(),
                    Value::Eq(..)
                ) {
                    return erase(
                        ctx,
                        &Term::Let {
                            ty: domain.clone(),
                            value: argument.clone(),
                            body: body.clone(),
                        }
                        .arc(),
                        kept,
                        budget,
                        demand,
                    );
                }
            }
            let ty = synth(ctx, function, budget)?;
            let Value::Pi(relevance, _, _) = ty.as_ref() else {
                return Err(Error::ExpectedFunction);
            };
            let f = erase(ctx, function, kept, budget, demand)?;
            if *relevance == Relevance::Erased {
                Ok(f)
            } else {
                Ok(RuntimeTerm::App(
                    Box::new(f),
                    Box::new(erase(
                        ctx,
                        argument,
                        kept,
                        budget,
                        ProofDemand::Computational,
                    )?),
                ))
            }
        }
        Term::Let { ty, value: v, body } => {
            let ty = value::eval(ty, &ctx.env, budget)?;
            let val = value::eval(v, &ctx.env, budget)?;
            // Proof lets may disappear when all their uses disappear. Try with
            // an unavailable runtime slot; keep the binding if usage requires it.
            if matches!(ty.as_ref(), Value::Eq(..)) {
                let mut discarded = kept.to_vec();
                discarded.push(false);
                match erase(
                    &ctx.define(ty.clone(), val.clone()),
                    body,
                    &discarded,
                    budget,
                    demand,
                ) {
                    Ok(body) => return Ok(body),
                    Err(Error::ErasedVariableUsed(_)) => {}
                    Err(error) => return Err(error),
                }
            }
            let rhs = erase(ctx, v, kept, budget, ProofDemand::Computational)?;
            let mut next = kept.to_vec();
            next.push(true);
            Ok(RuntimeTerm::Let(
                Box::new(rhs),
                Box::new(erase(&ctx.define(ty, val), body, &next, budget, demand)?),
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
        Term::Data { op, .. } => Err(Error::UnsupportedInductiveRuntime(op.id())),
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
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
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
        erase(ctx, &term, kept, budget, ProofDemand::Computational)
    };
    Ok(match ty.as_ref() {
        Value::Data { op, .. } => return Err(Error::UnsupportedInductiveRuntime(op.id())),
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
