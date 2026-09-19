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
    Data(u64, usize, Vec<Self>),
    DataElim {
        id: u64,
        recursion: Vec<Vec<Option<usize>>>,
        branches: Vec<Self>,
        value: Box<Self>,
    },
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
    erase_typed(ctx, term, kept, budget, demand, None)
}
fn erase_typed(
    ctx: &Context,
    term: &Tm,
    kept: &[bool],
    budget: &mut Budget,
    demand: ProofDemand,
    known_type: Option<Val>,
) -> Result<RuntimeTerm, Error> {
    budget.tick()?;
    let ty = match known_type {
        Some(ty) => ty,
        None => synth(ctx, term, budget)?,
    };
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

        Term::Pair { fst, snd, .. } => prim("pair", vec![sub(fst)?, sub(snd)?]),
        Term::Fst(p) => prim("fst", vec![sub(p)?]),
        Term::Snd(p) => prim("snd", vec![sub(p)?]),
        Term::Data { op, arguments } => {
            use crate::DataOp;
            let decl = budget
                .2
                .get(&op.id())
                .cloned()
                .ok_or(Error::UnknownInductive(op.id()))?;
            let p = decl.parameters.len();
            let mut sub = |t: &Tm| erase(ctx, t, kept, budget, ProofDemand::Computational);
            match *op {
                DataOp::Type(_) => Ok(RuntimeTerm::Unit),
                DataOp::Constructor(id, c) => {
                    // The whole input was checked before erasure. Reuse each
                    // field's declared type instead of rechecking every subtree.
                    let mut env = arguments[..p]
                        .iter()
                        .map(|arg| value::eval(arg, &ctx.env, budget))
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut fields = vec![];
                    for (domain, argument) in
                        decl.constructors[c].fields.iter().zip(&arguments[p..])
                    {
                        let ty = value::eval(domain, &env, budget)?;
                        fields.push(erase_typed(
                            ctx,
                            argument,
                            kept,
                            budget,
                            ProofDemand::Computational,
                            Some(ty),
                        )?);
                        env.push(value::eval(argument, &ctx.env, budget)?);
                    }
                    Ok(RuntimeTerm::Data(id, c, fields))
                }
                DataOp::Absurd(_) => prim("absurd", vec![sub(arguments.last().unwrap())?]),
                DataOp::Eliminate(id, _) => {
                    let start = p + decl.indices.len() + 1;
                    let branches = arguments[start..arguments.len() - 1]
                        .iter()
                        .map(&mut sub)
                        .collect::<Result<_, _>>()?;
                    let value = Box::new(sub(arguments.last().unwrap())?);
                    let mut recursion = vec![];
                    let mut params = vec![];
                    for argument in &arguments[..p] {
                        params.push(value::eval(argument, &ctx.env, budget)?);
                    }
                    for ctor in &decl.constructors {
                        let mut env = params.clone();
                        let mut fields = vec![];
                        for field in &ctor.fields {
                            let mut ty = value::eval(field, &env, budget)?;
                            let mut depth = 0;
                            let mut level = ctx.env.len() + env.len();
                            while let Value::Pi(relevance, _, body) = ty.as_ref() {
                                depth += usize::from(*relevance == Relevance::Runtime);
                                ty = body.apply(value::fresh(level), budget)?;
                                level += 1;
                            }
                            fields.push(if matches!(ty.as_ref(), Value::Data { op: DataOp::Type(other), .. } if *other == id) {
                                Some(depth)
                            } else { None });
                            env.push(value::fresh(ctx.env.len() + env.len()));
                        }
                        recursion.push(fields);
                    }
                    Ok(RuntimeTerm::DataElim {
                        id,
                        recursion,
                        branches,
                        value,
                    })
                }
            }
        }
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
        | Term::Inductive { .. } => Ok(RuntimeTerm::Unit),
    }
}

/// Runtime boundary schemas. Dependent sizes are checked using retained values.
/// Unknown type parameters accept only canonical immutable opaque data. Higher
/// order boundaries and sizes requiring erased indices are deliberately rejected.
#[derive(Clone, Debug)]
pub enum RuntimeType {
    Opaque,
    /// A schema supplied for a type parameter in a declaration template.
    Parameter(usize),
    /// Retained first-order value supplied to a family template.
    Value(RuntimeTerm),
    Data(u64, Vec<Self>, Vec<RuntimeTerm>),
    Type,
    Nat,
    Proof,
    Vec(Box<Self>, RuntimeTerm),
    Fin(RuntimeTerm),
    Pair(Box<Self>, Box<Self>),
    Function(Box<Self>, Box<Self>),
    Record(crate::InductiveId, Vec<Self>),
}
#[derive(Clone, Debug)]
pub struct RuntimeDataConstructor {
    pub fields: Vec<RuntimeType>,
    pub indices: Vec<RuntimeTerm>,
}
#[derive(Clone, Debug)]
pub struct RuntimeDataDeclaration {
    pub parameters: usize,
    pub constructors: Vec<RuntimeDataConstructor>,
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
    schema_with_parameters(ctx, ty, kept, budget, &[])
}
fn schema_with_parameters(
    ctx: &Context,
    ty: &Val,
    kept: &[bool],
    budget: &mut Budget,
    parameters: &[usize],
) -> Result<RuntimeType, Error> {
    budget.tick()?;
    let mut index = |v| {
        let term = value::quote(v, ctx.env.len(), budget)?;
        erase(ctx, &term, kept, budget, ProofDemand::Computational)
    };
    Ok(match ty.as_ref() {
        Value::Data {
            op: crate::DataOp::Type(id),
            arguments,
        } => {
            // Native representations are boundary adapters for checked standard
            // declarations, not additional typing or computation rules.
            match *id {
                crate::standard::NAT => return Ok(RuntimeType::Nat),
                id if crate::standard::vector_level(id).is_some() => {
                    let len = index(&arguments[1])?;
                    return Ok(RuntimeType::Vec(
                        Box::new(schema_with_parameters(
                            ctx,
                            &arguments[0],
                            kept,
                            budget,
                            parameters,
                        )?),
                        len,
                    ));
                }
                crate::standard::FIN => return Ok(RuntimeType::Fin(index(&arguments[0])?)),
                _ => {}
            }
            let decl = budget
                .2
                .get(id)
                .cloned()
                .ok_or(Error::UnknownInductive(*id))?;
            let p = decl.parameters.len();
            let mut param_env = vec![];
            let mut params = vec![];
            for (ty, arg) in decl.parameters.iter().zip(arguments) {
                let domain = value::eval(ty, &param_env, budget)?;
                if matches!(domain.as_ref(), Value::Universe(_)) {
                    params.push(schema_with_parameters(ctx, arg, kept, budget, parameters)?);
                } else {
                    runtime_index_type(&domain, budget, &mut std::collections::HashSet::new())?;
                    let term = value::quote(arg, ctx.env.len(), budget)?;
                    params.push(RuntimeType::Value(erase(
                        ctx,
                        &term,
                        kept,
                        budget,
                        ProofDemand::Computational,
                    )?));
                }
                param_env.push(arg.clone());
            }
            let mut indices = vec![];
            let mut index_env = param_env;
            for (domain, arg) in decl.indices.iter().zip(&arguments[p..]) {
                let domain = value::eval(domain, &index_env, budget)?;
                runtime_index_type(&domain, budget, &mut std::collections::HashSet::new())?;
                index_env.push(arg.clone());
                let term = value::quote(arg, ctx.env.len(), budget)?;
                indices.push(erase(ctx, &term, kept, budget, ProofDemand::Computational)?);
            }
            RuntimeType::Data(*id, params, indices)
        }
        Value::Universe(_) => RuntimeType::Type,

        Value::Eq(..) => RuntimeType::Proof,

        Value::Sigma(domain, codomain) => {
            let fst = schema_with_parameters(ctx, domain, kept, budget, parameters)?;
            let next_ty = codomain.apply(value::fresh(ctx.env.len()), budget)?;
            let mut next_kept = kept.to_vec();
            next_kept.push(true);
            let snd = schema_with_parameters(
                &ctx.bind(domain.clone()),
                &next_ty,
                &next_kept,
                budget,
                parameters,
            )?;
            RuntimeType::Pair(Box::new(fst), Box::new(snd))
        }
        Value::Pi(Relevance::Runtime, domain, codomain) => {
            let argument = schema_with_parameters(ctx, domain, kept, budget, parameters)?;
            let next = codomain.apply(value::fresh(ctx.env.len()), budget)?;
            let mut kept = kept.to_vec();
            kept.push(true);
            let result = schema_with_parameters(
                &ctx.bind(domain.clone()),
                &next,
                &kept,
                budget,
                parameters,
            )?;
            RuntimeType::Function(Box::new(argument), Box::new(result))
        }
        Value::Inductive {
            id,
            parameters: arguments,
        } => {
            let decl = ctx.globals.get(id).ok_or(Error::UnknownInductive(*id))?;
            let mut env = arguments.clone();
            let mut field_ctx = ctx.clone();
            let mut field_kept = kept.to_vec();
            let mut fields = vec![];
            for field in &decl.fields {
                let ty = value::eval(field, &env, budget)?;
                fields.push(schema_with_parameters(
                    &field_ctx,
                    &ty,
                    &field_kept,
                    budget,
                    parameters,
                )?);
                env.push(value::fresh(field_ctx.env.len()));
                field_ctx = field_ctx.bind(ty);
                field_kept.push(true);
            }
            RuntimeType::Record(*id, fields)
        }
        // A bare type parameter is opaque. An arbitrary neutral type family may
        // change representation; silently treating it as opaque would be unsafe.
        Value::Neutral(value::Neutral::Var(level)) if parameters.contains(level) => {
            RuntimeType::Parameter(kept[*level + 1..].iter().filter(|x| **x).count())
        }
        Value::Neutral(value::Neutral::Var(_)) => RuntimeType::Opaque,
        _ => return Err(Error::UnsupportedRuntimeBoundary),
    })
}

impl Kernel {
    /// Finite boundary template; recursive families are references, not unfolded schemas.
    pub fn runtime_data_declaration(&self, id: u64) -> Result<RuntimeDataDeclaration, Error> {
        let decl = self.data_declaration(id)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let mut ctx = self.context();
        let mut parameters = vec![];
        for ty in &decl.parameters {
            let ty = value::eval(ty, &ctx.env, &mut budget)?;
            if matches!(ty.as_ref(), Value::Universe(_)) {
                parameters.push(ctx.env.len());
            } else {
                runtime_index_type(&ty, &mut budget, &mut std::collections::HashSet::new())?;
            }
            ctx = ctx.bind(ty);
        }
        let mut constructors = vec![];
        for ctor in &decl.constructors {
            let mut ctx = ctx.clone();
            let mut fields = vec![];
            for field in &ctor.fields {
                let ty = value::eval(field, &ctx.env, &mut budget)?;
                fields.push(schema_with_parameters(
                    &ctx,
                    &ty,
                    &vec![true; ctx.env.len()],
                    &mut budget,
                    &parameters,
                )?);
                ctx = ctx.bind(ty);
            }
            let indices = ctor
                .indices
                .iter()
                .map(|index| {
                    erase(
                        &ctx,
                        index,
                        &vec![true; ctx.env.len()],
                        &mut budget,
                        ProofDemand::Computational,
                    )
                })
                .collect::<Result<_, _>>()?;
            constructors.push(RuntimeDataConstructor { fields, indices });
        }
        Ok(RuntimeDataDeclaration {
            parameters: decl.parameters.len(),
            constructors,
        })
    }
}

// Index equality at the Python boundary must not identify core values whose
// runtime representation was erased (types, proofs, or functions).
fn runtime_index_type(
    ty: &Val,
    budget: &mut Budget,
    visiting: &mut std::collections::HashSet<u64>,
) -> Result<(), Error> {
    budget.tick()?;
    match ty.as_ref() {
        Value::Data {
            op: crate::DataOp::Type(id),
            arguments,
        } => {
            let decl = budget
                .2
                .get(id)
                .cloned()
                .ok_or(Error::UnknownInductive(*id))?;
            // Inspect instantiated carriers before cutting recursive cycles:
            // List[List[Eq[...]]] must not hide proof erasure behind the same ID.
            let mut parameter_env = vec![];
            for (domain, parameter) in decl.parameters.iter().zip(arguments) {
                let domain = value::eval(domain, &parameter_env, budget)?;
                runtime_index_type(
                    if matches!(domain.as_ref(), Value::Universe(_)) {
                        parameter
                    } else {
                        &domain
                    },
                    budget,
                    visiting,
                )?;
                parameter_env.push(parameter.clone());
            }
            if !visiting.insert(*id) {
                return Ok(());
            }
            for ctor in &decl.constructors {
                let mut env = arguments[..decl.parameters.len()].to_vec();
                for field in &ctor.fields {
                    let ty = value::eval(field, &env, budget)?;
                    runtime_index_type(&ty, budget, visiting)?;
                    env.push(value::fresh(env.len()));
                }
            }
            visiting.remove(id);
            Ok(())
        }
        _ => Err(Error::UnsupportedRuntimeBoundary),
    }
}
