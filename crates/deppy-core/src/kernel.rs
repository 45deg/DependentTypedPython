pub(crate) mod data;
mod dependencies;
mod erasure;
use crate::value::{self, Budget, Env, Val, Value};
use crate::{Term, Tm};
pub use erasure::{RuntimeSignature, RuntimeTerm, RuntimeType};
use std::{fmt, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnknownDefinition(crate::DefId),
    AxiomHasNoRuntimeValue(crate::DefId),
    DuplicateDefinition(crate::DefId),
    UnknownInductive(crate::InductiveId),
    DuplicateInductive(crate::InductiveId),
    ArityMismatch,
    InvalidPositivity,
    FieldUniverseTooLarge,
    UnboundVariable(usize),
    ExpectedUniverse,
    ErasedVariableUsed(usize),
    UnsupportedRuntimeBoundary,
    UnsupportedInductiveRuntime(u64),
    ExpectedFunction,
    ExpectedSigma,
    ExpectedNat,
    ExpectedVec,
    ExpectedFin,
    ExpectedEmptyFin,
    ExpectedEmptyInductive,
    ExpectedEquality,
    TypeMismatch { expected: Tm, actual: Tm },
    UniverseOverflow,
    EscapingVariable,
    BudgetExceeded,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AxiomHasNoRuntimeValue(id) => {
                write!(f, "axiom {id} has no runtime implementation")
            }
            Self::UnknownDefinition(id) => write!(f, "unknown definition {id}"),
            Self::DuplicateDefinition(id) => write!(f, "definition {id} already exists"),
            Self::UnknownInductive(id) => write!(f, "unknown inductive declaration {id}"),
            Self::DuplicateInductive(id) => write!(f, "inductive declaration {id} already exists"),
            Self::InvalidPositivity => write!(
                f,
                "recursive occurrence is not strictly positive and uniform"
            ),
            Self::ArityMismatch => write!(f, "wrong number of parameters or fields"),
            Self::FieldUniverseTooLarge => {
                write!(f, "field universe exceeds the declared inductive universe")
            }
            Self::UnboundVariable(i) => write!(f, "unbound core variable {i}"),
            Self::UnsupportedInductiveRuntime(id) => write!(
                f,
                "general inductive runtime projection is not implemented for family {id}"
            ),
            Self::UnsupportedRuntimeBoundary => write!(
                f,
                "unsupported higher-order or type-family runtime boundary"
            ),
            Self::ErasedVariableUsed(i) => {
                write!(f, "erased variable {i} used in runtime computation")
            }
            Self::ExpectedUniverse => write!(f, "expected a type (a term inhabiting a universe)"),
            Self::ExpectedEquality => write!(f, "expected an equality proof"),
            Self::ExpectedVec => write!(f, "expected a vector"),
            Self::ExpectedFin => write!(f, "expected a finite index"),
            Self::ExpectedEmptyInductive => write!(
                f,
                "cannot prove every constructor impossible at these indices"
            ),
            Self::ExpectedEmptyFin => write!(f, "expected an impossible Fin Z value"),
            Self::ExpectedNat => write!(f, "expected a natural number"),
            Self::ExpectedSigma => write!(f, "expected a dependent pair"),
            Self::ExpectedFunction => write!(f, "expected a dependent function"),
            Self::TypeMismatch { expected, actual } => {
                write!(f, "type mismatch: expected {expected:?}, got {actual:?}")
            }
            Self::UniverseOverflow => write!(f, "universe level exceeds the supported range"),
            Self::EscapingVariable => write!(f, "semantic variable escapes its scope"),
            Self::BudgetExceeded => write!(f, "checking budget exhausted; result is unknown"),
        }
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Default)]
pub(crate) struct Context {
    globals: Arc<std::collections::BTreeMap<crate::InductiveId, crate::InductiveDecl>>,
    types: Vec<Val>,
    env: Env,
}
impl Context {
    fn bind(&self, ty: Val) -> Self {
        self.define(ty, value::fresh(self.env.len()))
    }
    fn define(&self, ty: Val, value: Val) -> Self {
        let mut next = self.clone();
        next.types.push(ty);
        next.env.push(value);
        next
    }
}

/// Public operations accept closed terms and always validate before evaluation.
/// A fresh shared operation budget is used for each call.
#[derive(Clone)]
pub struct Kernel {
    definitions: Arc<std::collections::BTreeMap<crate::DefId, crate::GlobalDeclaration>>,
    globals: Arc<std::collections::BTreeMap<crate::InductiveId, crate::InductiveDecl>>,
    data: Arc<std::collections::BTreeMap<u64, crate::DataDecl>>,
    max_steps: usize,
}
impl Default for Kernel {
    fn default() -> Self {
        Self::new(100_000)
    }
}
impl Kernel {
    pub fn new(max_steps: usize) -> Self {
        Self {
            max_steps,
            data: Arc::default(),
            globals: Arc::default(),
            definitions: Arc::default(),
        }
    }

    pub fn definition(&self, id: crate::DefId) -> Result<&crate::GlobalDeclaration, Error> {
        self.definitions
            .get(&id)
            .ok_or(Error::UnknownDefinition(id))
    }
    /// Check against the existing environment before insertion. No replacement,
    /// forward references or recursive definitions are accepted.
    pub fn define(&mut self, id: crate::DefId, definition: crate::Definition) -> Result<(), Error> {
        self.define_with_transparency(id, definition, crate::Transparency::Transparent)
    }

    /// Check a body before registering a constant opaque to conversion.
    pub fn define_opaque(
        &mut self,
        id: crate::DefId,
        definition: crate::Definition,
    ) -> Result<(), Error> {
        self.define_with_transparency(id, definition, crate::Transparency::Opaque)
    }

    fn define_with_transparency(
        &mut self,
        id: crate::DefId,
        definition: crate::Definition,
        transparency: crate::Transparency,
    ) -> Result<(), Error> {
        if self.definitions.contains_key(&id) {
            return Err(Error::DuplicateDefinition(id));
        }
        self.check(&definition.body, &definition.ty)?;
        Arc::make_mut(&mut self.definitions).insert(
            id,
            crate::GlobalDeclaration {
                ty: definition.ty,
                body: Some(definition.body),
                transparency,
            },
        );
        Ok(())
    }

    /// Register an explicitly assumed, well-formed type without a proof body.
    /// Axioms are neutral during reduction and do not add equality reflection.
    pub fn declare_axiom(&mut self, id: crate::DefId, ty: Tm) -> Result<(), Error> {
        if self.definitions.contains_key(&id) {
            return Err(Error::DuplicateDefinition(id));
        }
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        universe(&self.context(), &ty, &mut budget)?;
        Arc::make_mut(&mut self.definitions).insert(
            id,
            crate::GlobalDeclaration {
                ty,
                body: None,
                transparency: crate::Transparency::Opaque,
            },
        );
        Ok(())
    }

    fn context(&self) -> Context {
        Context {
            globals: self.globals.clone(),
            ..Context::default()
        }
    }
    pub fn declaration(&self, id: crate::InductiveId) -> Result<&crate::InductiveDecl, Error> {
        self.globals.get(&id).ok_or(Error::UnknownInductive(id))
    }
    /// Register a nonrecursive, unindexed single-constructor inductive.
    /// The new ID is unavailable while checking, forbidding self/forward references.
    pub fn declare(
        &mut self,
        id: crate::InductiveId,
        decl: crate::InductiveDecl,
    ) -> Result<(), Error> {
        if self.globals.contains_key(&id) {
            return Err(Error::DuplicateInductive(id));
        }
        decl.level.checked_add(1).ok_or(Error::UniverseOverflow)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let mut ctx = self.context();
        for ty in &decl.parameters {
            universe(&ctx, ty, &mut budget)?;
            let val = value::eval(ty, &ctx.env, &mut budget)?;
            ctx = ctx.bind(val);
        }
        for ty in &decl.fields {
            if universe(&ctx, ty, &mut budget)? > decl.level {
                return Err(Error::FieldUniverseTooLarge);
            }
            let val = value::eval(ty, &ctx.env, &mut budget)?;
            ctx = ctx.bind(val);
        }
        Arc::make_mut(&mut self.globals).insert(id, decl);
        Ok(())
    }
    pub fn infer(&self, term: &Tm) -> Result<Tm, Error> {
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let ty = synth(&self.context(), term, &mut budget)?;
        value::quote(&ty, 0, &mut budget)
    }

    pub fn check(&self, term: &Tm, ty: &Tm) -> Result<(), Error> {
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let ctx = self.context();
        universe(&ctx, ty, &mut budget)?;
        let expected = value::eval(ty, &ctx.env, &mut budget)?;
        check(&ctx, term, &expected, &mut budget)
    }

    pub fn normalize(&self, term: &Tm) -> Result<Tm, Error> {
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let ctx = self.context();
        synth(&ctx, term, &mut budget)?;
        let val = value::eval(term, &ctx.env, &mut budget)?;
        value::quote(&val, 0, &mut budget)
    }

    /// Both operands must inhabit the supplied type before conversion is tried.
    pub fn equivalent(&self, left: &Tm, right: &Tm, ty: &Tm) -> Result<bool, Error> {
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let ctx = self.context();
        universe(&ctx, ty, &mut budget)?;
        let ty = value::eval(ty, &ctx.env, &mut budget)?;
        check(&ctx, left, &ty, &mut budget)?;
        check(&ctx, right, &ty, &mut budget)?;
        let left = value::eval(left, &ctx.env, &mut budget)?;
        let right = value::eval(right, &ctx.env, &mut budget)?;
        value::equal_at(&ty, &left, &right, 0, &mut budget)
    }
}

fn universe(ctx: &Context, term: &Tm, budget: &mut Budget) -> Result<u32, Error> {
    match synth(ctx, term, budget)?.as_ref() {
        Value::Universe(level) => Ok(*level),
        _ => Err(Error::ExpectedUniverse),
    }
}

fn check(ctx: &Context, term: &Tm, expected: &Val, budget: &mut Budget) -> Result<(), Error> {
    let actual = synth(ctx, term, budget)?;
    if value::equal(&actual, expected, ctx.env.len(), budget)? {
        Ok(())
    } else {
        Err(Error::TypeMismatch {
            expected: value::quote(expected, ctx.env.len(), budget)?,
            actual: value::quote(&actual, ctx.env.len(), budget)?,
        })
    }
}

fn synth(ctx: &Context, term: &Tm, budget: &mut Budget) -> Result<Val, Error> {
    budget.tick()?;
    match term.as_ref() {
        Term::Data { op, arguments } => data::synth_data(ctx, *op, arguments, budget),
        Term::Global(id) => {
            let ty = budget
                .1
                .get(id)
                .ok_or(Error::UnknownDefinition(*id))?
                .ty
                .clone();
            value::eval(&ty, &vec![], budget)
        }
        Term::Inductive { id, parameters } => {
            let decl = ctx.globals.get(id).ok_or(Error::UnknownInductive(*id))?;
            arguments(ctx, parameters, &decl.parameters, vec![], budget)?;
            Ok(Arc::new(Value::Universe(decl.level)))
        }
        Term::Constructor {
            id,
            parameters,
            fields,
        } => {
            let decl = ctx.globals.get(id).ok_or(Error::UnknownInductive(*id))?;
            let params = arguments(ctx, parameters, &decl.parameters, vec![], budget)?;
            arguments(ctx, fields, &decl.fields, params.clone(), budget)?;
            Ok(Arc::new(Value::Inductive {
                id: *id,
                parameters: params,
            }))
        }
        Term::Elim {
            id,
            parameters,
            level,
            motive,
            branch,
            scrutinee,
        } => {
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            let decl = ctx.globals.get(id).ok_or(Error::UnknownInductive(*id))?;
            let params = arguments(ctx, parameters, &decl.parameters, vec![], budget)?;
            let nominal = Arc::new(Value::Inductive {
                id: *id,
                parameters: params.clone(),
            });
            check(ctx, scrutinee, &nominal, budget)?;
            let motive_ty = pi(
                value::quote(&nominal, ctx.env.len(), budget)?,
                Term::Universe(*level).arc(),
            );
            check(
                ctx,
                motive,
                &value::eval(&motive_ty, &ctx.env, budget)?,
                budget,
            )?;
            let motive_val = value::eval(motive, &ctx.env, budget)?;
            let mut env = params.clone();
            let mut fields = vec![];
            let mut domains = vec![];
            for ty in &decl.fields {
                let domain = value::eval(ty, &env, budget)?;
                let depth = ctx.env.len() + fields.len();
                domains.push(value::quote(&domain, depth, budget)?);
                let field = value::fresh(depth);
                env.push(field.clone());
                fields.push(field);
            }
            let constructor = Arc::new(Value::Constructor {
                id: *id,
                parameters: params,
                fields,
            });
            let result = value::apply(&motive_val, constructor, budget)?;
            let mut branch_ty = value::quote(&result, ctx.env.len() + domains.len(), budget)?;
            for domain in domains.into_iter().rev() {
                branch_ty = pi(domain, branch_ty);
            }
            check(
                ctx,
                branch,
                &value::eval(&branch_ty, &ctx.env, budget)?,
                budget,
            )?;
            value::apply(
                &motive_val,
                value::eval(scrutinee, &ctx.env, budget)?,
                budget,
            )
        }
        Term::Sigma { domain, codomain } => {
            let a = universe(ctx, domain, budget)?;
            let domain = value::eval(domain, &ctx.env, budget)?;
            let b = universe(&ctx.bind(domain), codomain, budget)?;
            Ok(Arc::new(Value::Universe(a.max(b))))
        }
        Term::Pair { ty, fst, snd } => {
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            let Value::Sigma(domain, codomain) = ty.as_ref() else {
                return Err(Error::ExpectedSigma);
            };
            check(ctx, fst, domain, budget)?;
            let second_ty = codomain.apply(value::eval(fst, &ctx.env, budget)?, budget)?;
            check(ctx, snd, &second_ty, budget)?;
            Ok(ty)
        }
        Term::Fst(pair) | Term::Snd(pair) => {
            let ty = synth(ctx, pair, budget)?;
            let Value::Sigma(domain, codomain) = ty.as_ref() else {
                return Err(Error::ExpectedSigma);
            };
            if matches!(term.as_ref(), Term::Fst(_)) {
                Ok(domain.clone())
            } else {
                let pair = value::eval(pair, &ctx.env, budget)?;
                codomain.apply(value::project(&pair, true, budget)?, budget)
            }
        }
        Term::Var(i) => ctx
            .types
            .len()
            .checked_sub(i.saturating_add(1))
            .and_then(|index| ctx.types.get(index))
            .cloned()
            .ok_or(Error::UnboundVariable(*i)),
        Term::Universe(level) => Ok(Arc::new(Value::Universe(
            level.checked_add(1).ok_or(Error::UniverseOverflow)?,
        ))),
        Term::NatElim {
            level,
            motive,
            zero,
            step,
            scrutinee,
        } => {
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            let motive_ty = Term::Pi {
                relevance: crate::Relevance::Runtime,
                domain: Term::Nat.arc(),
                codomain: Term::Universe(*level).arc(),
            }
            .arc();
            let motive_ty = value::eval(&motive_ty, &ctx.env, budget)?;
            check(ctx, motive, &motive_ty, budget)?;
            let motive = value::eval(motive, &ctx.env, budget)?;
            let zero_ty = value::apply(&motive, Arc::new(Value::Zero), budget)?;
            check(ctx, zero, &zero_ty, budget)?;

            // Evaluate a closed template in an environment extended by P.
            // Under n, P is #1; under n and ih, P is #2 and n is #1.
            let step_ty = Term::Pi {
                relevance: crate::Relevance::Runtime,
                domain: Term::Nat.arc(),
                codomain: Term::Pi {
                    relevance: crate::Relevance::Runtime,
                    domain: Term::App {
                        function: Term::Var(1).arc(),
                        argument: Term::Var(0).arc(),
                    }
                    .arc(),
                    codomain: Term::App {
                        function: Term::Var(2).arc(),
                        argument: Term::Succ(Term::Var(1).arc()).arc(),
                    }
                    .arc(),
                }
                .arc(),
            }
            .arc();
            let mut env = ctx.env.clone();
            env.push(motive.clone());
            let step_ty = value::eval(&step_ty, &env, budget)?;
            check(ctx, step, &step_ty, budget)?;
            check(ctx, scrutinee, &Arc::new(Value::Nat), budget)?;
            let n = value::eval(scrutinee, &ctx.env, budget)?;
            value::apply(&motive, n, budget)
        }
        Term::Eq { ty, left, right } => {
            let level = universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, left, &ty, budget)?;
            check(ctx, right, &ty, budget)?;
            Ok(Arc::new(Value::Universe(level)))
        }
        Term::Refl { ty, value: x } => {
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, x, &ty, budget)?;
            let x = value::eval(x, &ctx.env, budget)?;
            Ok(Arc::new(Value::Eq(ty, x.clone(), x)))
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
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, left, &ty, budget)?;
            check(ctx, right, &ty, budget)?;
            let left = value::eval(left, &ctx.env, budget)?;
            let right = value::eval(right, &ctx.env, budget)?;
            // A and x are semantic parameters, independent of surrounding binders.
            let env = vec![ty.clone(), left.clone()];
            let motive_ty = Term::Pi {
                relevance: crate::Relevance::Runtime,
                domain: Term::Var(1).arc(),
                codomain: Term::Pi {
                    relevance: crate::Relevance::Runtime,
                    domain: Term::Eq {
                        ty: Term::Var(2).arc(),
                        left: Term::Var(1).arc(),
                        right: Term::Var(0).arc(),
                    }
                    .arc(),
                    codomain: Term::Universe(*level).arc(),
                }
                .arc(),
            }
            .arc();
            let motive_ty = value::eval(&motive_ty, &env, budget)?;
            check(ctx, motive, &motive_ty, budget)?;
            let motive = value::eval(motive, &ctx.env, budget)?;
            let refl = Arc::new(Value::Refl(ty.clone(), left.clone()));
            let at_left = value::apply(&motive, left.clone(), budget)?;
            let base_ty = value::apply(&at_left, refl, budget)?;
            check(ctx, base, &base_ty, budget)?;
            check(
                ctx,
                proof,
                &Arc::new(Value::Eq(ty, left, right.clone())),
                budget,
            )?;
            let proof = value::eval(proof, &ctx.env, budget)?;
            let at_right = value::apply(&motive, right, budget)?;
            value::apply(&at_right, proof, budget)
        }
        Term::Vec { ty, len } => {
            let level = universe(ctx, ty, budget)?;
            check(ctx, len, &Arc::new(Value::Nat), budget)?;
            Ok(Arc::new(Value::Universe(level)))
        }
        Term::VNil { ty } => {
            universe(ctx, ty, budget)?;
            Ok(Arc::new(Value::Vec {
                ty: value::eval(ty, &ctx.env, budget)?,
                len: Arc::new(Value::Zero),
            }))
        }
        Term::VCons {
            ty,
            len,
            head,
            tail,
        } => {
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, len, &Arc::new(Value::Nat), budget)?;
            let len = value::eval(len, &ctx.env, budget)?;
            check(ctx, head, &ty, budget)?;
            check(
                ctx,
                tail,
                &Arc::new(Value::Vec {
                    ty: ty.clone(),
                    len: len.clone(),
                }),
                budget,
            )?;
            Ok(Arc::new(Value::Vec {
                ty,
                len: Arc::new(Value::Succ(len)),
            }))
        }
        Term::Fin { bound } => {
            check(ctx, bound, &Arc::new(Value::Nat), budget)?;
            Ok(Arc::new(Value::Universe(0)))
        }
        Term::FZ { bound } => {
            check(ctx, bound, &Arc::new(Value::Nat), budget)?;
            let bound = value::eval(bound, &ctx.env, budget)?;
            Ok(Arc::new(Value::Fin {
                bound: Arc::new(Value::Succ(bound)),
            }))
        }
        Term::FS { bound, pred } => {
            check(ctx, bound, &Arc::new(Value::Nat), budget)?;
            let bound = value::eval(bound, &ctx.env, budget)?;
            check(
                ctx,
                pred,
                &Arc::new(Value::Fin {
                    bound: bound.clone(),
                }),
                budget,
            )?;
            Ok(Arc::new(Value::Fin {
                bound: Arc::new(Value::Succ(bound)),
            }))
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
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, len, &Arc::new(Value::Nat), budget)?;
            let len = value::eval(len, &ctx.env, budget)?;
            check(
                ctx,
                scrutinee,
                &Arc::new(Value::Vec {
                    ty: ty.clone(),
                    len: len.clone(),
                }),
                budget,
            )?;
            let xs = value::eval(scrutinee, &ctx.env, budget)?;
            // Template environment [A]; after n, A is #1 and n is #0.
            let motive_ty = pi(
                Term::Nat.arc(),
                pi(
                    Term::Vec {
                        ty: var(1),
                        len: var(0),
                    }
                    .arc(),
                    Term::Universe(*level).arc(),
                ),
            );
            let motive_ty = value::eval(&motive_ty, &vec![ty.clone()], budget)?;
            check(ctx, motive, &motive_ty, budget)?;
            let motive = value::eval(motive, &ctx.env, budget)?;
            let nil_ty = apply2(
                &motive,
                Arc::new(Value::Zero),
                Arc::new(Value::VNil { ty: ty.clone() }),
                budget,
            )?;
            check(ctx, nil, &nil_ty, budget)?;
            // Template environment [A,P], followed by k,h,t,ih.
            let cons_ty = pi(
                Term::Nat.arc(),
                pi(
                    var(2),
                    pi(
                        Term::Vec {
                            ty: var(3),
                            len: var(1),
                        }
                        .arc(),
                        pi(
                            app2(var(3), var(2), var(0)),
                            app2(
                                var(4),
                                Term::Succ(var(3)).arc(),
                                Term::VCons {
                                    ty: var(5),
                                    len: var(3),
                                    head: var(2),
                                    tail: var(1),
                                }
                                .arc(),
                            ),
                        ),
                    ),
                ),
            );
            let cons_ty = value::eval(&cons_ty, &vec![ty, motive.clone()], budget)?;
            check(ctx, cons, &cons_ty, budget)?;
            apply2(&motive, len, xs, budget)
        }
        Term::FinElim {
            level,
            motive,
            zero,
            step,
            bound,
            scrutinee,
        } => {
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            check(ctx, bound, &Arc::new(Value::Nat), budget)?;
            let bound = value::eval(bound, &ctx.env, budget)?;
            check(
                ctx,
                scrutinee,
                &Arc::new(Value::Fin {
                    bound: bound.clone(),
                }),
                budget,
            )?;
            let index = value::eval(scrutinee, &ctx.env, budget)?;
            let motive_ty = pi(
                Term::Nat.arc(),
                pi(
                    Term::Fin { bound: var(0) }.arc(),
                    Term::Universe(*level).arc(),
                ),
            );
            let motive_ty = value::eval(&motive_ty, &vec![], budget)?;
            check(ctx, motive, &motive_ty, budget)?;
            let motive = value::eval(motive, &ctx.env, budget)?;
            // Template environment [P]. FZ carries the predecessor bound k.
            let zero_ty = pi(
                Term::Nat.arc(),
                app2(
                    var(1),
                    Term::Succ(var(0)).arc(),
                    Term::FZ { bound: var(0) }.arc(),
                ),
            );
            let zero_ty = value::eval(&zero_ty, &vec![motive.clone()], budget)?;
            check(ctx, zero, &zero_ty, budget)?;
            // After k,i,ih: P is #3, k is #2, i is #1.
            let step_ty = pi(
                Term::Nat.arc(),
                pi(
                    Term::Fin { bound: var(0) }.arc(),
                    pi(
                        app2(var(2), var(1), var(0)),
                        app2(
                            var(3),
                            Term::Succ(var(2)).arc(),
                            Term::FS {
                                bound: var(2),
                                pred: var(1),
                            }
                            .arc(),
                        ),
                    ),
                ),
            );
            let step_ty = value::eval(&step_ty, &vec![motive.clone()], budget)?;
            check(ctx, step, &step_ty, budget)?;
            apply2(&motive, bound, index, budget)
        }
        Term::Fin0Elim { ty, absurd } => {
            universe(ctx, ty, budget)?;
            check(
                ctx,
                absurd,
                &Arc::new(Value::Fin {
                    bound: Arc::new(Value::Zero),
                }),
                budget,
            )?;
            value::eval(ty, &ctx.env, budget)
        }
        Term::Nat => Ok(Arc::new(Value::Universe(0))),
        Term::Zero => Ok(Arc::new(Value::Nat)),
        Term::Succ(n) => {
            let nat = Arc::new(Value::Nat);
            check(ctx, n, &nat, budget)?;
            Ok(nat)
        }
        Term::Pi {
            domain, codomain, ..
        } => {
            let a = universe(ctx, domain, budget)?;
            let domain = value::eval(domain, &ctx.env, budget)?;
            let b = universe(&ctx.bind(domain), codomain, budget)?;
            Ok(Arc::new(Value::Universe(a.max(b))))
        }
        Term::Lam {
            relevance,
            domain,
            body,
        } => {
            universe(ctx, domain, budget)?;
            let dom = value::eval(domain, &ctx.env, budget)?;
            let body_ty = synth(&ctx.bind(dom), body, budget)?;
            let codomain = value::quote(&body_ty, ctx.env.len() + 1, budget)?;
            let pi = Term::Pi {
                relevance: *relevance,
                domain: domain.clone(),
                codomain,
            }
            .arc();
            value::eval(&pi, &ctx.env, budget)
        }
        Term::App { function, argument } => {
            let fun_ty = synth(ctx, function, budget)?;
            match fun_ty.as_ref() {
                Value::Pi(_, domain, codomain) => {
                    check(ctx, argument, domain, budget)?;
                    codomain.apply(value::eval(argument, &ctx.env, budget)?, budget)
                }
                _ => Err(Error::ExpectedFunction),
            }
        }
        Term::Let { ty, value, body } => {
            universe(ctx, ty, budget)?;
            let ty = value::eval(ty, &ctx.env, budget)?;
            check(ctx, value, &ty, budget)?;
            let val = value::eval(value, &ctx.env, budget)?;
            synth(&ctx.define(ty, val), body, budget)
        }
    }
}

// Small de Bruijn templates are evaluated with semantic parameters, avoiding
// any shifting of caller syntax while building dependent eliminator signatures.
fn var(index: usize) -> Tm {
    Term::Var(index).arc()
}
fn pi(domain: Tm, codomain: Tm) -> Tm {
    Term::Pi {
        relevance: crate::Relevance::Runtime,
        domain,
        codomain,
    }
    .arc()
}
fn app2(function: Tm, a: Tm, b: Tm) -> Tm {
    Term::App {
        function: Term::App {
            function,
            argument: a,
        }
        .arc(),
        argument: b,
    }
    .arc()
}
fn apply2(function: &Val, a: Val, b: Val, budget: &mut Budget) -> Result<Val, Error> {
    value::apply(&value::apply(function, a, budget)?, b, budget)
}

fn arguments(
    ctx: &Context,
    args: &[Tm],
    types: &[Tm],
    mut env: Env,
    budget: &mut Budget,
) -> Result<Env, Error> {
    if args.len() != types.len() {
        return Err(Error::ArityMismatch);
    }
    for (arg, ty) in args.iter().zip(types) {
        let ty = value::eval(ty, &env, budget)?;
        check(ctx, arg, &ty, budget)?;
        env.push(value::eval(arg, &ctx.env, budget)?);
    }
    Ok(env)
}
