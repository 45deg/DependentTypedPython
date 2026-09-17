//! Conservative lowering of a programmatic function HIR. No Python parsing.
mod rewrite;
use crate::{Elaborated, Elaborator, Error, Expr as E, Plicity};
use std::collections::{HashMap, HashSet};
type Env = HashMap<String, E>;

#[derive(Clone, Debug)]
pub struct Parameter {
    pub name: String,
    pub plicity: Plicity,
    pub ty: E,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub parameters: Vec<Parameter>,
    pub result: E,
    /// The parameter inspected by the outer match and checked for strict descent.
    pub decreases: String,
    /// Concrete universe of the motive's result, including generalized parameters.
    pub motive_level: u32,
    pub body: Body,
}
#[derive(Clone, Debug)]
pub enum Body {
    Return(E),
    Match { scrutinee: String, arms: Vec<Arm> },
}
#[derive(Clone, Debug)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: Body,
}
#[derive(Clone, Debug)]
pub enum Pattern {
    Zero,
    Succ(String),
    VNil,
    VCons {
        len: String,
        head: String,
        tail: String,
    },
    FZ(String),
    FS {
        bound: String,
        pred: String,
    },
}
#[derive(Clone)]
struct Recursion {
    ih: String,
    arguments: Vec<Option<String>>,
    suffix: Vec<Plicity>,
}
struct Lowerer {
    remaining: usize,
    next: usize,
}
#[derive(Clone)]
enum Kind {
    Nat,
    Vec { carrier: E, index: usize },
    Fin { index: usize },
}
impl Kind {
    fn index(&self) -> Option<usize> {
        match self {
            Self::Nat => None,
            Self::Vec { index, .. } | Self::Fin { index } => Some(*index),
        }
    }
}
impl Elaborator {
    pub fn compile_function(&self, function: &Function) -> Result<Elaborated, Error> {
        self.infer(&self.lower_function(function)?)
    }
    /// Produce an annotated AST; `compile_function` additionally elaborates and kernel-checks it.
    pub fn lower_function(&self, function: &Function) -> Result<E, Error> {
        Lowerer {
            remaining: self.max_steps,
            next: 0,
        }
        .function(function)
    }
}
impl Lowerer {
    fn tick(&mut self) -> Result<(), Error> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Error::BudgetExceeded)?;
        Ok(())
    }
    fn fresh(&mut self) -> String {
        let n = self.next;
        self.next += 1;
        format!("\0lower{n}")
    }
    fn name(name: &str) -> Result<(), Error> {
        if name.is_empty() || name.contains('\0') {
            Err(Error::InvalidDeclarationName(name.into()))
        } else {
            Ok(())
        }
    }
    fn bind(&mut self, env: &mut Env, name: &str) -> Result<String, Error> {
        Self::name(name)?;
        let fresh = self.fresh();
        env.insert(name.into(), E::name(&fresh));
        Ok(fresh)
    }
    fn function(&mut self, f: &Function) -> Result<E, Error> {
        self.tick()?;
        let d = f
            .parameters
            .iter()
            .position(|p| p.name == f.decreases)
            .ok_or_else(|| Error::InvalidRecursion("unknown decreases parameter".into()))?;
        let mut env = Env::new();
        let mut parameters = vec![];
        for p in &f.parameters {
            if env.contains_key(&p.name) {
                return Err(Error::InvalidDeclarationName(p.name.clone()));
            }
            let ty = self.rewrite(&p.ty, &env, None)?;
            let name = self.bind(&mut env, &p.name)?;
            parameters.push(Parameter {
                name,
                plicity: p.plicity,
                ty,
            });
        }
        let result = self.rewrite(&f.result, &env, None)?;
        let signature = pis(&parameters, result.clone());
        let E::Name(scrutinee) = env[&f.decreases].clone() else {
            unreachable!()
        };
        let kind = match &f.parameters[d].ty {
            E::Nat => Kind::Nat,
            E::Vec { ty, len } => {
                let index = self.index(f, d, len)?;
                let mut fixed = env.clone();
                fixed.remove(&f.parameters[index].name);
                Kind::Vec {
                    carrier: self.rewrite(ty, &fixed, None)?,
                    index,
                }
            }
            E::Fin { bound } => Kind::Fin {
                index: self.index(f, d, bound)?,
            },
            _ => {
                return Err(Error::UnsupportedMatch(
                    "decreases must have a direct Nat, Vec or Fin type".into(),
                ))
            }
        };
        if let Some(index) = kind.index() {
            // Prefix parameters remain fixed. Dependencies on the refined index
            // must occur after the scrutinee so they can be generalized.
            let mut fixed = env.clone();
            fixed.remove(&f.parameters[index].name);
            for p in &f.parameters[index + 1..d] {
                self.rewrite(&p.ty, &fixed, None)?;
            }
        }
        let body = match &f.body {
            Body::Return(value) => self.rewrite(value, &env, None)?,
            Body::Match {
                scrutinee: subject,
                arms,
            } => {
                if subject != &f.decreases {
                    return Err(Error::UnsupportedMatch(
                        "outer match must inspect the decreases parameter".into(),
                    ));
                }
                let (base, step) = coverage(&kind, arms)?;
                let k = self.fresh();
                let item = self.fresh();
                let mut motive_env = env.clone();
                motive_env.insert(
                    f.decreases.clone(),
                    E::name(if matches!(kind, Kind::Nat) { &k } else { &item }),
                );
                if let Some(index) = kind.index() {
                    motive_env.insert(f.parameters[index].name.clone(), E::name(&k));
                }
                let motive_result = self.generalized_type(f, d, &motive_env)?;
                let motive = if matches!(kind, Kind::Nat) {
                    lambda(&k, motive_result)
                } else {
                    lambda(&k, lambda(&item, motive_result))
                };
                let base = self.arm(f, d, &kind, base, &env, &parameters)?;
                let step = self.arm(f, d, &kind, step, &env, &parameters)?;
                let elim = match &kind {
                    Kind::Nat => {
                        E::nat_elim(f.motive_level, motive, base, step, E::name(&scrutinee))
                    }
                    Kind::Vec { carrier, index } => E::vec_elim(
                        f.motive_level,
                        carrier.clone(),
                        motive,
                        base,
                        step,
                        E::name(&parameters[*index].name),
                        E::name(&scrutinee),
                    ),
                    Kind::Fin { index } => E::fin_elim(
                        f.motive_level,
                        motive,
                        base,
                        step,
                        E::name(&parameters[*index].name),
                        E::name(&scrutinee),
                    ),
                };
                parameters[d + 1..]
                    .iter()
                    .fold(elim, |fun, p| apply(fun, E::name(&p.name), p.plicity))
            }
        };
        Ok(lambdas(&parameters, body).ann(signature))
    }
    fn index(&mut self, f: &Function, d: usize, index: &E) -> Result<usize, Error> {
        let E::Name(name) = index else {
            return Err(Error::UnsupportedMatch(
                "indexed scrutinee needs an earlier Nat parameter as its index".into(),
            ));
        };
        f.parameters[..d]
            .iter()
            .position(|p| p.name == *name && matches!(p.ty, E::Nat))
            .ok_or_else(|| {
                Error::UnsupportedMatch("index must name an earlier Nat parameter".into())
            })
    }
    fn generalized_type(&mut self, f: &Function, d: usize, env: &Env) -> Result<E, Error> {
        let mut env = env.clone();
        let mut suffix = vec![];
        for p in &f.parameters[d + 1..] {
            let ty = self.rewrite(&p.ty, &env, None)?;
            let name = self.bind(&mut env, &p.name)?;
            suffix.push(Parameter {
                name,
                ty,
                plicity: p.plicity,
            });
        }
        Ok(pis(&suffix, self.rewrite(&f.result, &env, None)?))
    }
    fn arm(
        &mut self,
        f: &Function,
        d: usize,
        kind: &Kind,
        arm: &Arm,
        outer: &Env,
        parameters: &[Parameter],
    ) -> Result<E, Error> {
        self.tick()?;
        let mut env = outer.clone();
        let mut bound = vec![];
        let mut seen = HashSet::new();
        let mut bind = |this: &mut Self, name: &str| -> Result<String, Error> {
            if f.parameters.iter().any(|p| p.name == name) {
                return Err(Error::InvalidPattern(
                    "pattern shadows a function parameter".into(),
                ));
            }
            if !seen.insert(name.to_owned()) {
                return Err(Error::InvalidPattern("duplicate pattern binding".into()));
            }
            let fresh = this.bind(&mut env, name)?;
            bound.push(fresh.clone());
            Ok(fresh)
        };
        let mut child = None;
        let mut predecessor = None;
        let constructor = match (&kind, &arm.pattern) {
            (Kind::Nat, Pattern::Zero) => E::Zero,
            (Kind::Nat, Pattern::Succ(name)) => {
                let k = bind(self, name)?;
                child = Some(k.clone());
                E::name(k).succ()
            }
            (Kind::Vec { carrier, .. }, Pattern::VNil) => {
                predecessor = Some(E::Zero);
                E::vnil(carrier.clone())
            }
            (Kind::Vec { carrier, .. }, Pattern::VCons { len, head, tail }) => {
                let k = bind(self, len)?;
                let h = bind(self, head)?;
                let t = bind(self, tail)?;
                child = Some(t.clone());
                predecessor = Some(E::name(&k).succ());
                E::vcons(carrier.clone(), E::name(k), E::name(h), E::name(t))
            }
            (Kind::Fin { .. }, Pattern::FZ(name)) => {
                let k = bind(self, name)?;
                predecessor = Some(E::name(&k).succ());
                E::fz(E::name(k))
            }
            (Kind::Fin { .. }, Pattern::FS { bound, pred }) => {
                let k = bind(self, bound)?;
                let j = bind(self, pred)?;
                child = Some(j.clone());
                predecessor = Some(E::name(&k).succ());
                E::fs(E::name(k), E::name(j))
            }
            _ => {
                return Err(Error::InvalidPattern(
                    "constructor does not belong to the scrutinee type".into(),
                ))
            }
        };
        // Pattern names may shadow outer names. Refinement is installed first,
        // then lexical pattern bindings win; the original identities stay private.
        let pattern_env = env.clone();
        env = outer.clone();
        env.insert(f.decreases.clone(), constructor);
        if let Some(index) = kind.index() {
            env.insert(f.parameters[index].name.clone(), predecessor.unwrap());
        }
        for name in &seen {
            env.insert(name.clone(), pattern_env[name].clone());
        }
        let recursion = if let Some(child) = child {
            let ih = self.fresh();
            let mut arguments = parameters
                .iter()
                .take(d + 1)
                .map(|p| Some(p.name.clone()))
                .collect::<Vec<_>>();
            arguments[d] = Some(child);
            if let Some(index) = kind.index() {
                arguments[index] = Some(bound[0].clone());
            }
            arguments.extend(f.parameters[d + 1..].iter().map(|_| None));
            bound.push(ih.clone());
            Some(Recursion {
                ih,
                arguments,
                suffix: f.parameters[d + 1..].iter().map(|p| p.plicity).collect(),
            })
        } else {
            None
        };
        let mut suffix = vec![];
        for p in &f.parameters[d + 1..] {
            // Parameter binders lexically precede the match: pattern shadowing
            // of a suffix name is unsupported rather than silently captured.
            if seen.contains(&p.name) {
                return Err(Error::InvalidPattern(
                    "pattern shadows a generalized parameter".into(),
                ));
            }
            let ty = self.rewrite(&p.ty, &env, None)?;
            let name = self.bind(&mut env, &p.name)?;
            suffix.push(Parameter {
                name,
                plicity: p.plicity,
                ty,
            });
        }
        let body = self.body(&arm.body, &env, recursion.as_ref())?;
        let body = lambdas(&suffix, body);
        Ok(bound.iter().rev().fold(body, |b, n| lambda(n, b)))
    }
    fn body(&mut self, body: &Body, env: &Env, recursion: Option<&Recursion>) -> Result<E, Error> {
        self.tick()?;
        match body {
            Body::Return(e) => self.rewrite(e, env, recursion),
            Body::Match { .. } => Err(Error::UnsupportedMatch(
                "nested matching is not supported here".into(),
            )),
        }
    }
}
fn lambda(name: &str, body: E) -> E {
    E::lam(name, Plicity::Explicit, None, body)
}
fn apply(fun: E, arg: E, p: Plicity) -> E {
    if p == Plicity::Explicit {
        fun.app(arg)
    } else {
        fun.implicit(arg)
    }
}
fn lambdas(ps: &[Parameter], body: E) -> E {
    ps.iter().rev().fold(body, |b, p| {
        E::lam(&p.name, p.plicity, Some(p.ty.clone()), b)
    })
}
fn pis(ps: &[Parameter], body: E) -> E {
    ps.iter()
        .rev()
        .fold(body, |b, p| E::pi(&p.name, p.plicity, p.ty.clone(), b))
}
fn coverage<'a>(kind: &Kind, arms: &'a [Arm]) -> Result<(&'a Arm, &'a Arm), Error> {
    let mut base = None;
    let mut step = None;
    for arm in arms {
        let slot = match (kind, &arm.pattern) {
            (Kind::Nat, Pattern::Zero)
            | (Kind::Vec { .. }, Pattern::VNil)
            | (Kind::Fin { .. }, Pattern::FZ(_)) => &mut base,
            (Kind::Nat, Pattern::Succ(_))
            | (Kind::Vec { .. }, Pattern::VCons { .. })
            | (Kind::Fin { .. }, Pattern::FS { .. }) => &mut step,
            _ => {
                return Err(Error::InvalidPattern(
                    "constructor does not belong to the scrutinee type".into(),
                ))
            }
        };
        if slot.replace(arm).is_some() {
            return Err(Error::InvalidPattern("duplicate constructor branch".into()));
        }
    }
    match (base, step) {
        (Some(a), Some(b)) => Ok((a, b)),
        _ => Err(Error::InvalidPattern(
            "match must cover both constructors".into(),
        )),
    }
}
