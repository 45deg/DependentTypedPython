use crate::value::{self, Budget, Env, Val, Value};
use crate::{Term, Tm};
use std::{fmt, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnboundVariable(usize),
    ExpectedUniverse,
    ExpectedFunction,
    TypeMismatch { expected: Tm, actual: Tm },
    UniverseOverflow,
    EscapingVariable,
    BudgetExceeded,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnboundVariable(i) => write!(f, "unbound core variable {i}"),
            Self::ExpectedUniverse => write!(f, "expected a type (a term inhabiting a universe)"),
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
struct Context {
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
pub struct Kernel {
    max_steps: usize,
}
impl Default for Kernel {
    fn default() -> Self {
        Self::new(100_000)
    }
}
impl Kernel {
    pub fn new(max_steps: usize) -> Self {
        Self { max_steps }
    }

    pub fn infer(&self, term: &Tm) -> Result<Tm, Error> {
        let mut budget = Budget(self.max_steps);
        let ty = synth(&Context::default(), term, &mut budget)?;
        value::quote(&ty, 0, &mut budget)
    }

    pub fn check(&self, term: &Tm, ty: &Tm) -> Result<(), Error> {
        let mut budget = Budget(self.max_steps);
        let ctx = Context::default();
        universe(&ctx, ty, &mut budget)?;
        let expected = value::eval(ty, &ctx.env, &mut budget)?;
        check(&ctx, term, &expected, &mut budget)
    }

    pub fn normalize(&self, term: &Tm) -> Result<Tm, Error> {
        let mut budget = Budget(self.max_steps);
        let ctx = Context::default();
        synth(&ctx, term, &mut budget)?;
        let val = value::eval(term, &ctx.env, &mut budget)?;
        value::quote(&val, 0, &mut budget)
    }

    /// Both operands must inhabit the supplied type before conversion is tried.
    pub fn equivalent(&self, left: &Tm, right: &Tm, ty: &Tm) -> Result<bool, Error> {
        let mut budget = Budget(self.max_steps);
        let ctx = Context::default();
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
