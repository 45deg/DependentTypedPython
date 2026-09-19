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
    Inductive {
        id: crate::InductiveId,
        parameters: Vec<Val>,
    },
    Constructor {
        id: crate::InductiveId,
        parameters: Vec<Val>,
        fields: Vec<Val>,
    },

    Sigma(Val, Closure),
    Pair(Val, Val, Val),
    Universe(u32),
    Eq(Val, Val, Val),
    Refl(Val, Val),
    Vec {
        ty: Val,
        len: Val,
    },
    VNil {
        ty: Val,
    },
    VCons {
        ty: Val,
        len: Val,
        head: Val,
        tail: Val,
    },
    Fin {
        bound: Val,
    },
    FZ {
        bound: Val,
    },
    FS {
        bound: Val,
        pred: Val,
    },
    Nat,
    Zero,
    Succ(Val),
    Pi(Relevance, Val, Closure),
    Lam(Relevance, Val, Closure),
    Neutral(Neutral),
}

pub(crate) enum Neutral {
    Elim {
        id: crate::InductiveId,
        parameters: Vec<Val>,
        level: u32,
        motive: Val,
        branch: Val,
        scrutinee: Val,
    },

    // Semantic variables use levels (counted from the outermost binder).
    Fst(Val),
    Snd(Val),
    Var(usize),
    Global(crate::DefId),
    App(Val, Val),
    J {
        level: u32,
        ty: Val,
        left: Val,
        motive: Val,
        base: Val,
        right: Val,
        proof: Val,
    },
    VecElim {
        level: u32,
        ty: Val,
        motive: Val,
        nil: Val,
        cons: Val,
        len: Val,
        scrutinee: Val,
    },
    FinElim {
        level: u32,
        motive: Val,
        zero: Val,
        step: Val,
        bound: Val,
        scrutinee: Val,
    },
    Fin0Elim {
        ty: Val,
        absurd: Val,
    },
    NatElim {
        level: u32,
        motive: Val,
        zero: Val,
        step: Val,
        scrutinee: Val,
    },
}

/// Shared across checking, evaluation and conversion. Exhaustion is an error.
pub(crate) struct Budget(
    pub usize,
    pub Arc<std::collections::BTreeMap<crate::DefId, crate::GlobalDeclaration>>,
);
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
        Term::Global(id) => {
            let body = budget
                .1
                .get(id)
                .ok_or(Error::UnknownDefinition(*id))?
                .unfolding_body()
                .cloned();
            if let Some(body) = body {
                return eval(&body, &vec![], budget);
            }
            Value::Neutral(Neutral::Global(*id))
        }
        Term::Inductive { id, parameters } => Value::Inductive {
            id: *id,
            parameters: parameters
                .iter()
                .map(|x| eval(x, env, budget))
                .collect::<Result<_, _>>()?,
        },
        Term::Constructor {
            id,
            parameters,
            fields,
        } => Value::Constructor {
            id: *id,
            parameters: parameters
                .iter()
                .map(|x| eval(x, env, budget))
                .collect::<Result<_, _>>()?,
            fields: fields
                .iter()
                .map(|x| eval(x, env, budget))
                .collect::<Result<_, _>>()?,
        },
        Term::Elim {
            id,
            parameters,
            level,
            motive,
            branch,
            scrutinee,
        } => {
            let parameters = parameters
                .iter()
                .map(|x| eval(x, env, budget))
                .collect::<Result<_, _>>()?;
            let motive = eval(motive, env, budget)?;
            let branch = eval(branch, env, budget)?;
            let scrutinee = eval(scrutinee, env, budget)?;
            if let Value::Constructor { fields, .. } = scrutinee.as_ref() {
                let mut result = branch;
                for field in fields {
                    result = apply(&result, field.clone(), budget)?;
                }
                return Ok(result);
            }
            Value::Neutral(Neutral::Elim {
                id: *id,
                parameters,
                level: *level,
                motive,
                branch,
                scrutinee,
            })
        }
        Term::Var(index) => {
            return env
                .len()
                .checked_sub(index.saturating_add(1))
                .and_then(|i| env.get(i))
                .cloned()
                .ok_or(Error::UnboundVariable(*index))
        }
        Term::Sigma { domain, codomain } => Value::Sigma(
            eval(domain, env, budget)?,
            Closure {
                env: env.clone(),
                body: codomain.clone(),
            },
        ),
        Term::Pair { ty, fst, snd } => Value::Pair(
            eval(ty, env, budget)?,
            eval(fst, env, budget)?,
            eval(snd, env, budget)?,
        ),
        Term::Fst(p) | Term::Snd(p) => {
            return project(
                &eval(p, env, budget)?,
                matches!(term.as_ref(), Term::Fst(_)),
                budget,
            )
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
        Term::Eq { ty, left, right } => Value::Eq(
            eval(ty, env, budget)?,
            eval(left, env, budget)?,
            eval(right, env, budget)?,
        ),
        Term::Refl { ty, value } => Value::Refl(eval(ty, env, budget)?, eval(value, env, budget)?),
        Term::J {
            level,
            ty,
            left,
            motive,
            base,
            right,
            proof,
        } => {
            let ty = eval(ty, env, budget)?;
            let left = eval(left, env, budget)?;
            let motive = eval(motive, env, budget)?;
            let base = eval(base, env, budget)?;
            let right = eval(right, env, budget)?;
            let proof = eval(proof, env, budget)?;
            match proof.as_ref() {
                Value::Refl(_, _) => return Ok(base),
                Value::Neutral(_) => Value::Neutral(Neutral::J {
                    level: *level,
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                }),
                _ => return Err(Error::ExpectedEquality),
            }
        }
        Term::Vec { ty, len } => Value::Vec {
            ty: eval(ty, env, budget)?,
            len: eval(len, env, budget)?,
        },
        Term::VNil { ty } => Value::VNil {
            ty: eval(ty, env, budget)?,
        },
        Term::VCons {
            ty,
            len,
            head,
            tail,
        } => Value::VCons {
            ty: eval(ty, env, budget)?,
            len: eval(len, env, budget)?,
            head: eval(head, env, budget)?,
            tail: eval(tail, env, budget)?,
        },
        Term::Fin { bound } => Value::Fin {
            bound: eval(bound, env, budget)?,
        },
        Term::FZ { bound } => Value::FZ {
            bound: eval(bound, env, budget)?,
        },
        Term::FS { bound, pred } => Value::FS {
            bound: eval(bound, env, budget)?,
            pred: eval(pred, env, budget)?,
        },
        Term::VecElim {
            level,
            ty,
            motive,
            nil,
            cons,
            len,
            scrutinee,
        } => {
            let rec = VecRec {
                level: *level,
                ty: eval(ty, env, budget)?,
                motive: eval(motive, env, budget)?,
                nil: eval(nil, env, budget)?,
                cons: eval(cons, env, budget)?,
            };
            return rec.apply(
                &eval(len, env, budget)?,
                &eval(scrutinee, env, budget)?,
                budget,
            );
        }
        Term::FinElim {
            level,
            motive,
            zero,
            step,
            bound,
            scrutinee,
        } => {
            let rec = FinRec {
                level: *level,
                motive: eval(motive, env, budget)?,
                zero: eval(zero, env, budget)?,
                step: eval(step, env, budget)?,
            };
            return rec.apply(
                &eval(bound, env, budget)?,
                &eval(scrutinee, env, budget)?,
                budget,
            );
        }
        Term::Fin0Elim { ty, absurd } => {
            let ty = eval(ty, env, budget)?;
            let absurd = eval(absurd, env, budget)?;
            if !matches!(absurd.as_ref(), Value::Neutral(_)) {
                return Err(Error::ExpectedEmptyFin);
            }
            Value::Neutral(Neutral::Fin0Elim { ty, absurd })
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
        (
            Value::Inductive { id, parameters },
            Value::Inductive {
                id: j,
                parameters: q,
            },
        ) => Ok(id == j && equal_list(parameters, q, depth, budget)?),
        (
            Value::Constructor {
                id,
                parameters,
                fields,
            },
            Value::Constructor {
                id: j,
                parameters: q,
                fields: g,
            },
        ) => Ok(id == j
            && equal_list(parameters, q, depth, budget)?
            && equal_list(fields, g, depth, budget)?),
        (
            Value::Neutral(Neutral::Elim {
                id,
                parameters,
                level,
                motive,
                branch,
                scrutinee,
            }),
            Value::Neutral(Neutral::Elim {
                id: j,
                parameters: q,
                level: l,
                motive: m,
                branch: b,
                scrutinee: s,
            }),
        ) => Ok(id == j
            && level == l
            && equal_list(parameters, q, depth, budget)?
            && equal(motive, m, depth, budget)?
            && equal(branch, b, depth, budget)?
            && equal(scrutinee, s, depth, budget)?),
        (Value::Sigma(a, b), Value::Sigma(c, d)) => {
            if !equal(a, c, depth, budget)? {
                return Ok(false);
            }
            let x = fresh(depth);
            equal(
                &b.apply(x.clone(), budget)?,
                &d.apply(x, budget)?,
                depth + 1,
                budget,
            )
        }
        (Value::Pair(t, a, b), Value::Pair(u, c, d)) => Ok(equal(t, u, depth, budget)?
            && equal(a, c, depth, budget)?
            && equal(b, d, depth, budget)?),
        (Value::Neutral(Neutral::Fst(a)), Value::Neutral(Neutral::Fst(b)))
        | (Value::Neutral(Neutral::Snd(a)), Value::Neutral(Neutral::Snd(b))) => {
            equal(a, b, depth, budget)
        }
        (Value::Eq(a, x, y), Value::Eq(b, u, v)) => Ok(equal(a, b, depth, budget)?
            && equal(x, u, depth, budget)?
            && equal(y, v, depth, budget)?),
        (Value::Refl(a, x), Value::Refl(b, y)) => {
            Ok(equal(a, b, depth, budget)? && equal(x, y, depth, budget)?)
        }
        (
            Value::Neutral(Neutral::J {
                level: l,
                ty: a,
                left: x,
                motive: c,
                base: d,
                right: y,
                proof: p,
            }),
            Value::Neutral(Neutral::J {
                level: l2,
                ty: a2,
                left: x2,
                motive: c2,
                base: d2,
                right: y2,
                proof: p2,
            }),
        ) => Ok(l == l2
            && equal(a, a2, depth, budget)?
            && equal(x, x2, depth, budget)?
            && equal(c, c2, depth, budget)?
            && equal(d, d2, depth, budget)?
            && equal(y, y2, depth, budget)?
            && equal(p, p2, depth, budget)?),
        (Value::Vec { ty, len }, Value::Vec { ty: ty2, len: len2 }) => {
            Ok(equal(ty, ty2, depth, budget)? && equal(len, len2, depth, budget)?)
        }
        (Value::VNil { ty }, Value::VNil { ty: ty2 }) => Ok(equal(ty, ty2, depth, budget)?),
        (
            Value::VCons {
                ty,
                len,
                head,
                tail,
            },
            Value::VCons {
                ty: ty2,
                len: len2,
                head: head2,
                tail: tail2,
            },
        ) => Ok(equal(ty, ty2, depth, budget)?
            && equal(len, len2, depth, budget)?
            && equal(head, head2, depth, budget)?
            && equal(tail, tail2, depth, budget)?),
        (Value::Fin { bound }, Value::Fin { bound: bound2 }) => {
            Ok(equal(bound, bound2, depth, budget)?)
        }
        (Value::FZ { bound }, Value::FZ { bound: bound2 }) => {
            Ok(equal(bound, bound2, depth, budget)?)
        }
        (
            Value::FS { bound, pred },
            Value::FS {
                bound: bound2,
                pred: pred2,
            },
        ) => Ok(equal(bound, bound2, depth, budget)? && equal(pred, pred2, depth, budget)?),
        (
            Value::Neutral(Neutral::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            }),
            Value::Neutral(Neutral::VecElim {
                level: level2,
                ty: ty2,
                motive: motive2,
                nil: nil2,
                cons: cons2,
                len: len2,
                scrutinee: scrutinee2,
            }),
        ) => Ok(level == level2
            && equal(ty, ty2, depth, budget)?
            && equal(motive, motive2, depth, budget)?
            && equal(nil, nil2, depth, budget)?
            && equal(cons, cons2, depth, budget)?
            && equal(len, len2, depth, budget)?
            && equal(scrutinee, scrutinee2, depth, budget)?),
        (
            Value::Neutral(Neutral::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            }),
            Value::Neutral(Neutral::FinElim {
                level: level2,
                motive: motive2,
                zero: zero2,
                step: step2,
                bound: bound2,
                scrutinee: scrutinee2,
            }),
        ) => Ok(level == level2
            && equal(motive, motive2, depth, budget)?
            && equal(zero, zero2, depth, budget)?
            && equal(step, step2, depth, budget)?
            && equal(bound, bound2, depth, budget)?
            && equal(scrutinee, scrutinee2, depth, budget)?),
        (
            Value::Neutral(Neutral::Fin0Elim { ty, absurd }),
            Value::Neutral(Neutral::Fin0Elim {
                ty: ty2,
                absurd: absurd2,
            }),
        ) => Ok(equal(ty, ty2, depth, budget)? && equal(absurd, absurd2, depth, budget)?),
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
        (Value::Neutral(Neutral::Global(x)), Value::Neutral(Neutral::Global(y))) => Ok(x == y),
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
        Value::Inductive { id, parameters } => Term::Inductive {
            id: *id,
            parameters: parameters
                .iter()
                .map(|x| quote(x, depth, budget))
                .collect::<Result<_, _>>()?,
        },
        Value::Constructor {
            id,
            parameters,
            fields,
        } => Term::Constructor {
            id: *id,
            parameters: parameters
                .iter()
                .map(|x| quote(x, depth, budget))
                .collect::<Result<_, _>>()?,
            fields: fields
                .iter()
                .map(|x| quote(x, depth, budget))
                .collect::<Result<_, _>>()?,
        },
        Value::Neutral(Neutral::Elim {
            id,
            parameters,
            level,
            motive,
            branch,
            scrutinee,
        }) => Term::Elim {
            id: *id,
            parameters: parameters
                .iter()
                .map(|x| quote(x, depth, budget))
                .collect::<Result<_, _>>()?,
            level: *level,
            motive: quote(motive, depth, budget)?,
            branch: quote(branch, depth, budget)?,
            scrutinee: quote(scrutinee, depth, budget)?,
        },
        Value::Sigma(domain, codomain) => Term::Sigma {
            domain: quote(domain, depth, budget)?,
            codomain: quote(&codomain.apply(fresh(depth), budget)?, depth + 1, budget)?,
        },
        Value::Pair(ty, fst, snd) => Term::Pair {
            ty: quote(ty, depth, budget)?,
            fst: quote(fst, depth, budget)?,
            snd: quote(snd, depth, budget)?,
        },
        Value::Neutral(Neutral::Fst(p)) => Term::Fst(quote(p, depth, budget)?),
        Value::Neutral(Neutral::Snd(p)) => Term::Snd(quote(p, depth, budget)?),
        Value::Universe(level) => Term::Universe(*level),
        Value::Eq(ty, left, right) => Term::Eq {
            ty: quote(ty, depth, budget)?,
            left: quote(left, depth, budget)?,
            right: quote(right, depth, budget)?,
        },
        Value::Refl(ty, value) => Term::Refl {
            ty: quote(ty, depth, budget)?,
            value: quote(value, depth, budget)?,
        },
        Value::Neutral(Neutral::J {
            level,
            ty,
            left,
            motive,
            base,
            right,
            proof,
        }) => Term::J {
            level: *level,
            ty: quote(ty, depth, budget)?,
            left: quote(left, depth, budget)?,
            motive: quote(motive, depth, budget)?,
            base: quote(base, depth, budget)?,
            right: quote(right, depth, budget)?,
            proof: quote(proof, depth, budget)?,
        },
        Value::Vec { ty, len } => Term::Vec {
            ty: quote(ty, depth, budget)?,
            len: quote(len, depth, budget)?,
        },
        Value::VNil { ty } => Term::VNil {
            ty: quote(ty, depth, budget)?,
        },
        Value::VCons {
            ty,
            len,
            head,
            tail,
        } => Term::VCons {
            ty: quote(ty, depth, budget)?,
            len: quote(len, depth, budget)?,
            head: quote(head, depth, budget)?,
            tail: quote(tail, depth, budget)?,
        },
        Value::Fin { bound } => Term::Fin {
            bound: quote(bound, depth, budget)?,
        },
        Value::FZ { bound } => Term::FZ {
            bound: quote(bound, depth, budget)?,
        },
        Value::FS { bound, pred } => Term::FS {
            bound: quote(bound, depth, budget)?,
            pred: quote(pred, depth, budget)?,
        },
        Value::Neutral(Neutral::VecElim {
            level,
            ty,
            motive,
            nil,
            cons,
            len,
            scrutinee,
        }) => Term::VecElim {
            level: *level,
            ty: quote(ty, depth, budget)?,
            motive: quote(motive, depth, budget)?,
            nil: quote(nil, depth, budget)?,
            cons: quote(cons, depth, budget)?,
            len: quote(len, depth, budget)?,
            scrutinee: quote(scrutinee, depth, budget)?,
        },
        Value::Neutral(Neutral::FinElim {
            level,
            motive,
            zero,
            step,
            bound,
            scrutinee,
        }) => Term::FinElim {
            level: *level,
            motive: quote(motive, depth, budget)?,
            zero: quote(zero, depth, budget)?,
            step: quote(step, depth, budget)?,
            bound: quote(bound, depth, budget)?,
            scrutinee: quote(scrutinee, depth, budget)?,
        },
        Value::Neutral(Neutral::Fin0Elim { ty, absurd }) => Term::Fin0Elim {
            ty: quote(ty, depth, budget)?,
            absurd: quote(absurd, depth, budget)?,
        },
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
        Value::Neutral(Neutral::Global(id)) => Term::Global(*id),
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

/// Structural recursion follows the tail, retaining its explicit size witness.
struct VecRec {
    level: u32,
    ty: Val,
    motive: Val,
    nil: Val,
    cons: Val,
}
impl VecRec {
    fn apply(&self, len: &Val, xs: &Val, budget: &mut Budget) -> Result<Val, Error> {
        budget.tick()?;
        match xs.as_ref() {
            Value::VNil { .. } => Ok(self.nil.clone()),
            Value::VCons {
                len, head, tail, ..
            } => {
                let ih = self.apply(len, tail, budget)?;
                let branch = apply(&self.cons, len.clone(), budget)?;
                let branch = apply(&branch, head.clone(), budget)?;
                let branch = apply(&branch, tail.clone(), budget)?;
                apply(&branch, ih, budget)
            }
            Value::Neutral(_) => Ok(Arc::new(Value::Neutral(Neutral::VecElim {
                level: self.level,
                ty: self.ty.clone(),
                motive: self.motive.clone(),
                nil: self.nil.clone(),
                cons: self.cons.clone(),
                len: len.clone(),
                scrutinee: xs.clone(),
            }))),
            _ => Err(Error::ExpectedVec),
        }
    }
}
struct FinRec {
    level: u32,
    motive: Val,
    zero: Val,
    step: Val,
}
impl FinRec {
    fn apply(&self, bound: &Val, index: &Val, budget: &mut Budget) -> Result<Val, Error> {
        budget.tick()?;
        match index.as_ref() {
            Value::FZ { bound } => apply(&self.zero, bound.clone(), budget),
            Value::FS { bound, pred } => {
                let ih = self.apply(bound, pred, budget)?;
                let branch = apply(&self.step, bound.clone(), budget)?;
                let branch = apply(&branch, pred.clone(), budget)?;
                apply(&branch, ih, budget)
            }
            Value::Neutral(_) => Ok(Arc::new(Value::Neutral(Neutral::FinElim {
                level: self.level,
                motive: self.motive.clone(),
                zero: self.zero.clone(),
                step: self.step.clone(),
                bound: bound.clone(),
                scrutinee: index.clone(),
            }))),
            _ => Err(Error::ExpectedFin),
        }
    }
}

pub(crate) fn project(pair: &Val, first: bool, budget: &mut Budget) -> Result<Val, Error> {
    budget.tick()?;
    match pair.as_ref() {
        Value::Pair(_, fst, snd) => Ok(if first { fst.clone() } else { snd.clone() }),
        Value::Neutral(_) => Ok(Arc::new(Value::Neutral(if first {
            Neutral::Fst(pair.clone())
        } else {
            Neutral::Snd(pair.clone())
        }))),
        _ => Err(Error::ExpectedSigma),
    }
}

fn equal_list(a: &[Val], b: &[Val], depth: usize, budget: &mut Budget) -> Result<bool, Error> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (a, b) in a.iter().zip(b) {
        if !equal(a, b, depth, budget)? {
            return Ok(false);
        }
    }
    Ok(true)
}
