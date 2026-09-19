//! Conservative lowering of a programmatic function HIR. No Python parsing.
mod data;
pub(crate) use data::lifted_cases;
mod nested;
mod rewrite;
mod specialize;
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
    Located {
        location: crate::SourceLocation,
        body: Box<Body>,
    },
    Return(E),
    /// Immutable definition, checked before any following match.
    Let {
        name: String,
        ty: Option<E>,
        value: E,
        body: Box<Body>,
    },
    Match {
        scrutinee: String,
        arms: Vec<Arm>,
    },
}
#[derive(Clone, Debug)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: Body,
}
#[derive(Clone, Debug)]
pub enum Pattern {
    Constructor {
        name: String,
        fields: Vec<String>,
    },
    Located {
        location: crate::SourceLocation,
        pattern: Box<Pattern>,
    },
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
impl Body {
    pub fn located(self, location: crate::SourceLocation) -> Self {
        Self::Located {
            location,
            body: Box::new(self),
        }
    }
    fn unlocated(&self) -> &Self {
        match self {
            Self::Located { body, .. } => body.unlocated(),
            body => body,
        }
    }
    fn locate_error(&self, error: Error) -> Error {
        match self {
            Self::Located { location, .. } => error.at(location),
            _ => error,
        }
    }
}
impl Pattern {
    pub fn located(self, location: crate::SourceLocation) -> Self {
        Self::Located {
            location,
            pattern: Box::new(self),
        }
    }
    fn unlocated(&self) -> &Self {
        match self {
            Self::Located { pattern, .. } => pattern.unlocated(),
            pattern => pattern,
        }
    }
    fn locate_error(&self, error: Error) -> Error {
        match self {
            Self::Located { location, .. } => error.at(location),
            _ => error,
        }
    }
}
#[derive(Clone)]
struct Local {
    name: String,
    ty: Option<E>,
    value: E,
}
type CheckedLocal = (String, Option<E>, E);

#[derive(Clone)]
struct Recursion {
    ih: E,
    history: Option<E>,
    target: usize,
    indices: Vec<usize>,
    signature: Option<E>,
    plicities: Vec<Plicity>,
    arguments: Vec<Option<String>>,
    suffix: Vec<Plicity>,
}
struct Lowerer {
    generated: bool,
    kernel: deppy_core::Kernel,
    family: Option<data::Family>,
    alternatives: Vec<Recursion>,
    remaining: usize,
    next: usize,
    globals: Env,
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
        let family = if let Some(d) = function
            .parameters
            .iter()
            .position(|p| p.name == function.decreases)
        {
            if matches!(
                function.parameters[d].ty.unlocated(),
                E::Nat | E::Vec { .. } | E::Fin { .. }
            ) {
                None
            } else {
                let signature = self.infer(&pis(&function.parameters, E::Universe(0)))?;
                let mut term = self.kernel.normalize(&signature.term)?;
                let mut prefix = vec![];
                for _ in 0..d {
                    let deppy_core::Term::Pi {
                        domain, codomain, ..
                    } = term.as_ref()
                    else {
                        return Err(Error::ExpectedFunction);
                    };
                    prefix.push(domain.clone());
                    term = codomain.clone();
                }
                if let deppy_core::Term::Pi { domain, .. } = term.as_ref() {
                    if let deppy_core::Term::Data {
                        op: deppy_core::DataOp::Type(id),
                        arguments,
                    } = domain.as_ref()
                    {
                        Some(data::Family {
                            id: *id,
                            arguments: arguments.clone(),
                            prefix,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        } else {
            None
        };
        Lowerer {
            generated: false,
            kernel: self.kernel.clone(),
            family,
            alternatives: vec![],
            remaining: self.max_steps,
            next: 0,
            globals: self
                .globals
                .iter()
                .map(|(name, id)| (name.clone(), E::Core(deppy_core::Term::Global(*id).arc())))
                .collect(),
        }
        .function(function)
    }
}
impl Lowerer {
    fn local(
        &mut self,
        local: &Local,
        env: &mut Env,
        recursion: Option<&Recursion>,
    ) -> Result<CheckedLocal, Error> {
        self.tick()?;
        // Do not shadow another local or pattern binding. Globals may be hidden.
        if env.get(&local.name).is_some_and(|value| {
            !matches!(value, E::Core(term) if matches!(term.as_ref(), deppy_core::Term::Global(_)))
        }) {
            return Err(Error::InvalidDeclarationName(local.name.clone()));
        }
        let ty = local
            .ty
            .as_ref()
            .map(|ty| self.rewrite(ty, env, recursion))
            .transpose()?;
        let value = self.rewrite(&local.value, env, recursion)?;
        let name = self.bind(env, &local.name)?;
        Ok((name, ty, value))
    }

    fn clear_locals(&self, locals: &[Local], env: &mut Env) {
        for local in locals {
            env.remove(&local.name);
            if let Some(global) = self.globals.get(&local.name) {
                env.insert(local.name.clone(), global.clone());
            }
        }
    }

    fn replay_locals(
        &mut self,
        locals: &[Local],
        env: &mut Env,
        recursion: Option<&Recursion>,
    ) -> Result<Vec<CheckedLocal>, Error> {
        self.clear_locals(locals, env);
        locals
            .iter()
            .map(|local| self.local(local, env, recursion))
            .collect()
    }

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
        if !self.generated {
            Self::name(name)?;
        }
        let fresh = format!("{}:{name}", self.fresh());
        env.insert(name.into(), E::name(&fresh));
        Ok(fresh)
    }
    fn function(&mut self, f: &Function) -> Result<E, Error> {
        self.tick()?;
        if let Some(family) = self.family.take() {
            return self.data_function(f, family);
        }
        let d = f
            .parameters
            .iter()
            .position(|p| p.name == f.decreases)
            .ok_or_else(|| Error::InvalidRecursion("unknown decreases parameter".into()))?;
        let mut env = self.globals.clone();
        let mut seen = HashSet::new();
        let mut parameters = vec![];
        for p in &f.parameters {
            if !seen.insert(p.name.clone()) {
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
        let kind = match f.parameters[d].ty.unlocated() {
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
        let mut source_body = &f.body;
        let mut locals = vec![];
        let mut checked = vec![];
        while let Body::Let {
            name,
            ty,
            value,
            body,
        } = source_body.unlocated()
        {
            let local = Local {
                name: name.clone(),
                ty: ty.clone(),
                value: value.clone(),
            };
            checked.push(self.local(&local, &mut env, None)?);
            locals.push(local);
            source_body = body;
        }
        let body = (|| -> Result<E, Error> {
            Ok(match source_body.unlocated() {
                Body::Let { .. } | Body::Located { .. } => unreachable!(),
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
                    self.clear_locals(&locals, &mut motive_env);
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
                    let base = self.arm(f, d, &kind, base, (&env, &parameters, &locals))?;
                    let step = self.arm(f, d, &kind, step, (&env, &parameters, &locals))?;
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
            })
        })()
        .map_err(|error| source_body.locate_error(error))?;
        Ok(lambdas(&parameters, wrap_locals(checked, body)).ann(signature))
    }
    fn index(&mut self, f: &Function, d: usize, index: &E) -> Result<usize, Error> {
        let E::Name(name) = index.unlocated() else {
            return Err(Error::UnsupportedMatch(
                "indexed scrutinee needs an earlier Nat parameter as its index".into(),
            ));
        };
        f.parameters[..d]
            .iter()
            .position(|p| p.name == *name && matches!(p.ty.unlocated(), E::Nat))
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
        context: (&Env, &[Parameter], &[Local]),
    ) -> Result<E, Error> {
        self.tick()?;
        let (outer, parameters, locals) = context;
        let mut env = outer.clone();
        self.clear_locals(locals, &mut env);
        let mut bound = vec![];
        let mut seen = HashSet::new();
        let mut bind = |this: &mut Self, name: &str| -> Result<String, Error> {
            if outer.contains_key(name) {
                return Err(arm.pattern.locate_error(Error::InvalidPattern(
                    "pattern shadows an existing binding".into(),
                )));
            }
            if !seen.insert(name.to_owned()) {
                return Err(arm
                    .pattern
                    .locate_error(Error::InvalidPattern("duplicate pattern binding".into())));
            }
            let fresh = this
                .bind(&mut env, name)
                .map_err(|error| arm.pattern.locate_error(error))?;
            bound.push(fresh.clone());
            Ok(fresh)
        };
        let mut child = None;
        let mut refined_index = None;
        let constructor = match (&kind, arm.pattern.unlocated()) {
            (Kind::Nat, Pattern::Zero) => E::Zero,
            (Kind::Nat, Pattern::Succ(name)) => {
                let k = bind(self, name)?;
                child = Some(k.clone());
                E::name(k).succ()
            }
            (Kind::Vec { carrier, .. }, Pattern::VNil) => {
                refined_index = Some(E::Zero);
                E::vnil(carrier.clone())
            }
            (Kind::Vec { carrier, .. }, Pattern::VCons { len, head, tail }) => {
                let k = bind(self, len)?;
                let h = bind(self, head)?;
                let t = bind(self, tail)?;
                child = Some(t.clone());
                refined_index = Some(E::name(&k).succ());
                E::vcons(carrier.clone(), E::name(k), E::name(h), E::name(t))
            }
            (Kind::Fin { .. }, Pattern::FZ(name)) => {
                let k = bind(self, name)?;
                refined_index = Some(E::name(&k).succ());
                E::fz(E::name(k))
            }
            (Kind::Fin { .. }, Pattern::FS { bound, pred }) => {
                let k = bind(self, bound)?;
                let j = bind(self, pred)?;
                child = Some(j.clone());
                refined_index = Some(E::name(&k).succ());
                E::fs(E::name(k), E::name(j))
            }
            _ => {
                return Err(arm.pattern.locate_error(Error::InvalidPattern(
                    "constructor does not belong to the scrutinee type".into(),
                )))
            }
        };
        // Pattern bindings are fresh and cannot shadow function parameters.
        // Refine both the scrutinee and its index before checking later binders.
        env.insert(f.decreases.clone(), constructor);
        if let Some(index) = kind.index() {
            env.insert(f.parameters[index].name.clone(), refined_index.unwrap());
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
                ih: E::name(ih),
                history: None,
                target: d,
                indices: kind.index().into_iter().collect(),
                signature: None,
                plicities: f.parameters.iter().map(|p| p.plicity).collect(),
                arguments,
                suffix: f.parameters[d + 1..].iter().map(|p| p.plicity).collect(),
            })
        } else {
            None
        };
        let mut suffix = vec![];
        for p in &f.parameters[d + 1..] {
            let ty = self.rewrite(&p.ty, &env, None)?;
            let name = self.bind(&mut env, &p.name)?;
            suffix.push(Parameter {
                name,
                plicity: p.plicity,
                ty,
            });
        }
        let checked = self.replay_locals(locals, &mut env, recursion.as_ref())?;
        let body = self.branch_body(f, &arm.body, &env, recursion.as_ref(), (&suffix, locals))?;
        let body = wrap_locals(checked, body);
        let body = lambdas(&suffix, body);
        Ok(bound.iter().rev().fold(body, |b, n| lambda(n, b)))
    }
}
// Keep the generic definitions as well as their refined branch instances:
// unused or ill-typed values must still be checked before specialization.
fn wrap_locals(locals: Vec<CheckedLocal>, body: E) -> E {
    locals
        .into_iter()
        .rev()
        .fold(body, |body, (name, ty, value)| {
            E::let_in(name, ty, value, body)
        })
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
        let slot = match (kind, arm.pattern.unlocated()) {
            (Kind::Nat, Pattern::Zero)
            | (Kind::Vec { .. }, Pattern::VNil)
            | (Kind::Fin { .. }, Pattern::FZ(_)) => &mut base,
            (Kind::Nat, Pattern::Succ(_))
            | (Kind::Vec { .. }, Pattern::VCons { .. })
            | (Kind::Fin { .. }, Pattern::FS { .. }) => &mut step,
            _ => {
                return Err(arm.pattern.locate_error(Error::InvalidPattern(
                    "constructor does not belong to the scrutinee type".into(),
                )))
            }
        };
        if slot.replace(arm).is_some() {
            return Err(arm
                .pattern
                .locate_error(Error::InvalidPattern("duplicate constructor branch".into())));
        }
    }
    match (base, step) {
        (Some(a), Some(b)) => Ok((a, b)),
        _ => Err(Error::InvalidPattern(
            "match must cover both constructors".into(),
        )),
    }
}
