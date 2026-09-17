use crate::{Error, Relevance, Term, Tm};
use std::sync::Arc;

pub(crate) type Val = Arc<Value>;
pub(crate) type Env = Vec<Val>;

#[derive(Clone)]
pub(crate) struct Closure {
    env: Env,
    body: Tm,
}

pub(crate) enum Value {
    Universe(u32),
    Nat,
    Zero,
    Succ(Val),
    Pi(Relevance, Val, Closure),
    Lam(Relevance, Val, Closure),
    Neutral(Neutral),
}

pub(crate) enum Neutral {
    // Semantic variables use levels (counted from the outermost binder).
    Var(usize),
    App(Val, Val),
    NatElim {
        level: u32,
        motive: Val,
        zero: Val,
        step: Val,
        scrutinee: Val,
    },
}

/// Shared across checking, evaluation and conversion. Exhaustion is an error.
pub(crate) struct Budget(pub usize);
impl Budget {
    pub fn tick(&mut self) -> Result<(), Error> {
        self.0 = self.0.checked_sub(1).ok_or(Error::BudgetExceeded)?;
        Ok(())
    }
}

pub(crate) fn fresh(level: usize) -> Val {
    Arc::new(Value::Neutral(Neutral::Var(level)))
}

impl Closure {
    pub fn apply(&self, arg: Val, budget: &mut Budget) -> Result<Val, Error> {
        let mut env = self.env.clone();
        env.push(arg);
        eval(&self.body, &env, budget)
    }
}

pub(crate) fn apply(fun: &Val, arg: Val, budget: &mut Budget) -> Result<Val, Error> {
    budget.tick()?;
    match fun.as_ref() {
        Value::Lam(_, _, body) => body.apply(arg, budget),
        Value::Neutral(_) => Ok(Arc::new(Value::Neutral(Neutral::App(fun.clone(), arg)))),
        _ => Err(Error::ExpectedFunction),
    }
}

pub(crate) fn eval(term: &Tm, env: &Env, budget: &mut Budget) -> Result<Val, Error> {
    budget.tick()?;
    Ok(Arc::new(match term.as_ref() {
        Term::Var(index) => {
            return env
                .len()
                .checked_sub(index.saturating_add(1))
                .and_then(|i| env.get(i))
                .cloned()
                .ok_or(Error::UnboundVariable(*index))
        }
        Term::Universe(level) => Value::Universe(*level),
        Term::NatElim {
            level,
            motive,
            zero,
            step,
            scrutinee,
        } => {
            let motive = eval(motive, env, budget)?;
            let zero = eval(zero, env, budget)?;
            let step = eval(step, env, budget)?;
            let scrutinee = eval(scrutinee, env, budget)?;
            return nat_elim(*level, &motive, &zero, &step, &scrutinee, budget);
        }
        Term::Nat => Value::Nat,
        Term::Zero => Value::Zero,
        Term::Succ(n) => Value::Succ(eval(n, env, budget)?),
        Term::Pi {
            relevance,
            domain,
            codomain,
        } => Value::Pi(
            *relevance,
            eval(domain, env, budget)?,
            Closure {
                env: env.clone(),
                body: codomain.clone(),
            },
        ),
        Term::Lam {
            relevance,
            domain,
            body,
        } => Value::Lam(
            *relevance,
            eval(domain, env, budget)?,
            Closure {
                env: env.clone(),
                body: body.clone(),
            },
        ),
        Term::App { function, argument } => {
            let fun = eval(function, env, budget)?;
            let arg = eval(argument, env, budget)?;
            return apply(&fun, arg, budget);
        }
        Term::Let { value, body, .. } => {
            let val = eval(value, env, budget)?;
            let mut env = env.clone();
            env.push(val);
            return eval(body, &env, budget);
        }
    }))
}

/// Conversion of already well-typed values; eta is restricted to functions.
/// Top-level term comparison is additionally directed by its checked type.
pub(crate) fn equal(a: &Val, b: &Val, depth: usize, budget: &mut Budget) -> Result<bool, Error> {
    budget.tick()?;
    match (a.as_ref(), b.as_ref()) {
        (Value::Universe(x), Value::Universe(y)) => Ok(x == y),
        (Value::Nat, Value::Nat) | (Value::Zero, Value::Zero) => Ok(true),
        (Value::Succ(x), Value::Succ(y)) => equal(x, y, depth, budget),
        (Value::Pi(r, dom, cod), Value::Pi(s, dom2, cod2)) => {
            if r != s || !equal(dom, dom2, depth, budget)? {
                return Ok(false);
            }
            let x = fresh(depth);
            equal(
                &cod.apply(x.clone(), budget)?,
                &cod2.apply(x, budget)?,
                depth + 1,
                budget,
            )
        }
        (Value::Lam(r, dom, body), Value::Lam(s, dom2, body2)) => {
            if r != s || !equal(dom, dom2, depth, budget)? {
                return Ok(false);
            }
            let x = fresh(depth);
            equal(
                &body.apply(x.clone(), budget)?,
                &body2.apply(x, budget)?,
                depth + 1,
                budget,
            )
        }
        (Value::Lam(_, _, body), Value::Neutral(_)) => {
            let x = fresh(depth);
            equal(
                &body.apply(x.clone(), budget)?,
                &apply(b, x, budget)?,
                depth + 1,
                budget,
            )
        }
        (Value::Neutral(_), Value::Lam(_, _, _)) => equal(b, a, depth, budget),
        (Value::Neutral(Neutral::Var(x)), Value::Neutral(Neutral::Var(y))) => Ok(x == y),
        (Value::Neutral(Neutral::App(f, x)), Value::Neutral(Neutral::App(g, y))) => {
            Ok(equal(f, g, depth, budget)? && equal(x, y, depth, budget)?)
        }
        (
            Value::Neutral(Neutral::NatElim {
                level: l,
                motive: p,
                zero: z,
                step: s,
                scrutinee: n,
            }),
            Value::Neutral(Neutral::NatElim {
                level: l2,
                motive: p2,
                zero: z2,
                step: s2,
                scrutinee: n2,
            }),
        ) => Ok(l == l2
            && equal(p, p2, depth, budget)?
            && equal(z, z2, depth, budget)?
            && equal(s, s2, depth, budget)?
            && equal(n, n2, depth, budget)?),
        _ => Ok(false),
    }
}

pub(crate) fn equal_at(
    ty: &Val,
    a: &Val,
    b: &Val,
    depth: usize,
    budget: &mut Budget,
) -> Result<bool, Error> {
    budget.tick()?;
    if let Value::Pi(_, _, cod) = ty.as_ref() {
        let x = fresh(depth);
        let result_ty = cod.apply(x.clone(), budget)?;
        equal_at(
            &result_ty,
            &apply(a, x.clone(), budget)?,
            &apply(b, x, budget)?,
            depth + 1,
            budget,
        )
    } else {
        equal(a, b, depth, budget)
    }
}

/// Reification produces beta/zeta normal forms, preserving lambda annotations.
pub(crate) fn quote(value: &Val, depth: usize, budget: &mut Budget) -> Result<Tm, Error> {
    budget.tick()?;
    Ok(match value.as_ref() {
        Value::Universe(level) => Term::Universe(*level),
        Value::Nat => Term::Nat,
        Value::Zero => Term::Zero,
        Value::Succ(n) => Term::Succ(quote(n, depth, budget)?),
        Value::Pi(relevance, domain, codomain) => Term::Pi {
            relevance: *relevance,
            domain: quote(domain, depth, budget)?,
            codomain: quote(&codomain.apply(fresh(depth), budget)?, depth + 1, budget)?,
        },
        Value::Lam(relevance, domain, body) => Term::Lam {
            relevance: *relevance,
            domain: quote(domain, depth, budget)?,
            body: quote(&body.apply(fresh(depth), budget)?, depth + 1, budget)?,
        },
        Value::Neutral(Neutral::NatElim {
            level,
            motive,
            zero,
            step,
            scrutinee,
        }) => Term::NatElim {
            level: *level,
            motive: quote(motive, depth, budget)?,
            zero: quote(zero, depth, budget)?,
            step: quote(step, depth, budget)?,
            scrutinee: quote(scrutinee, depth, budget)?,
        },
        Value::Neutral(Neutral::Var(level)) => Term::Var(
            depth
                .checked_sub(level + 1)
                .ok_or(Error::EscapingVariable)?,
        ),
        Value::Neutral(Neutral::App(function, argument)) => Term::App {
            function: quote(function, depth, budget)?,
            argument: quote(argument, depth, budget)?,
        },
    }
    .arc())
}

/// Primitive structural recursion. A neutral scrutinee remains a neutral
/// eliminator; no eta rule for Nat or arbitrary recursion is introduced.
fn nat_elim(
    level: u32,
    motive: &Val,
    zero: &Val,
    step: &Val,
    n: &Val,
    budget: &mut Budget,
) -> Result<Val, Error> {
    budget.tick()?;
    match n.as_ref() {
        Value::Zero => Ok(zero.clone()),
        Value::Succ(pred) => {
            let ih = nat_elim(level, motive, zero, step, pred, budget)?;
            apply(&apply(step, pred.clone(), budget)?, ih, budget)
        }
        Value::Neutral(_) => Ok(Arc::new(Value::Neutral(Neutral::NatElim {
            level,
            motive: motive.clone(),
            zero: zero.clone(),
            step: step.clone(),
            scrutinee: n.clone(),
        }))),
        _ => Err(Error::ExpectedNat),
    }
}
