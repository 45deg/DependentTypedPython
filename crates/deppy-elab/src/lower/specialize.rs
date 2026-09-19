//! Rigid index-pattern specialization. The motive computes a harmless inhabited
//! type outside the requested indices, so impossible branches require no axiom.
use super::data::{instantiated, nested_match, Family};
use super::*;
use deppy_core::{DataOp, Term, Tm};

#[derive(Clone)]
enum IndexPattern {
    Bind(String),
    Constructor {
        family: u64,
        constructor: usize,
        parameters: Vec<E>,
        fields: Vec<Self>,
    },
}
#[derive(Clone)]
struct Symbolic {
    expression: E,
    shape: Shape,
}
#[derive(Clone)]
enum Shape {
    Variable,
    Constructor(u64, usize, Vec<Symbolic>),
}
fn unit_type(level: u32) -> E {
    if level == 0 {
        E::Nat
    } else {
        E::Universe(level - 1)
    }
}
fn unit_value(level: u32) -> E {
    match level {
        0 => E::Zero,
        1 => E::Nat,
        n => E::Universe(n - 2),
    }
}
type Leaf<'a> = dyn FnMut(&mut Lowerer, &Env) -> Result<E, Error> + 'a;

impl Lowerer {
    fn index_pattern(
        &mut self,
        term: &Tm,
        prefix: &[Tm],
        values: &[E],
        names: &[Parameter],
        seen: &mut HashSet<String>,
    ) -> Result<IndexPattern, Error> {
        match term.as_ref() {
            Term::Var(i) if *i < names.len() => {
                let name = names[names.len() - 1 - i].name.clone();
                if !seen.insert(name.clone()) {
                    return Err(Error::UnsupportedMatch(
                        "index patterns must be linear".into(),
                    ));
                }
                Ok(IndexPattern::Bind(name))
            }
            Term::Data {
                op: DataOp::Constructor(id, c),
                arguments,
            } => {
                let decl = self.kernel.data_declaration(*id)?;
                let p = decl.parameters.len();
                let parameters = arguments[..p]
                    .iter()
                    .map(|t| instantiated(prefix, t.clone(), values.iter().cloned()))
                    .collect();
                let fields = arguments[p..]
                    .iter()
                    .map(|t| self.index_pattern(t, prefix, values, names, seen))
                    .collect::<Result<_, _>>()?;
                Ok(IndexPattern::Constructor {
                    family: *id,
                    constructor: *c,
                    parameters,
                    fields,
                })
            }
            _ => Err(Error::UnsupportedMatch(
                "an index must normalize to a linear constructor pattern".into(),
            )),
        }
    }
    fn symbolic(&mut self, term: &Tm, telescope: &[Tm], values: &[E]) -> Result<Symbolic, Error> {
        if let Term::Var(i) = term.as_ref() {
            return Ok(Symbolic {
                expression: values[values.len() - 1 - i].clone(),
                shape: Shape::Variable,
            });
        }
        let expression = instantiated(telescope, term.clone(), values.iter().cloned());
        let shape = if let Term::Data {
            op: DataOp::Constructor(id, c),
            arguments,
        } = term.as_ref()
        {
            let p = self.kernel.data_declaration(*id)?.parameters.len();
            Shape::Constructor(
                *id,
                *c,
                arguments[p..]
                    .iter()
                    .map(|t| self.symbolic(t, telescope, values))
                    .collect::<Result<_, _>>()?,
            )
        } else {
            return Err(Error::UnsupportedMatch(
                "constructor result indices must normalize to variables or constructors".into(),
            ));
        };
        Ok(Symbolic { expression, shape })
    }
    fn index_decision(
        &mut self,
        mut pending: Vec<(IndexPattern, Symbolic)>,
        mut env: Env,
        level: u32,
        success: &mut Leaf<'_>,
        failure: &E,
    ) -> Result<E, Error> {
        self.tick()?;
        let Some((pattern, value)) = pending.pop() else {
            return success(self, &env);
        };
        let IndexPattern::Constructor {
            family,
            constructor,
            parameters,
            fields,
        } = pattern
        else {
            let IndexPattern::Bind(name) = pattern else {
                unreachable!()
            };
            env.insert(name, value.expression);
            return self.index_decision(pending, env, level, success, failure);
        };
        if let Shape::Constructor(id, c, actual) = value.shape {
            if id != family || c != constructor {
                return Ok(failure.clone());
            }
            pending.extend(fields.into_iter().zip(actual));
            return self.index_decision(pending, env, level, success, failure);
        }
        let declaration = self.kernel.data_declaration(family)?;
        let mut branches = vec![];
        for (c, ctor) in declaration.constructors.iter().enumerate() {
            let bound = ctor.fields.iter().map(|_| self.fresh()).collect::<Vec<_>>();
            let body = if c == constructor {
                let mut next = pending.clone();
                next.extend(
                    fields
                        .iter()
                        .cloned()
                        .zip(bound.iter().map(|name| Symbolic {
                            expression: E::name(name),
                            shape: Shape::Variable,
                        })),
                );
                self.index_decision(next, env.clone(), level, success, failure)?
            } else {
                failure.clone()
            };
            branches.push(crate::CaseBranch {
                constructor: crate::CaseConstructor::Core(family, c),
                fields: bound,
                body,
                location: None,
            });
        }
        let _ = parameters; // Parameters are inferred from the checked receiver type.
        Ok(E::Cases {
            level,
            value: Box::new(value.expression),
            branches,
            generalize: vec![],
        })
    }

    pub(super) fn specialized_data_function(
        &mut self,
        f: &Function,
        family: Family,
    ) -> Result<E, Error> {
        let d = f
            .parameters
            .iter()
            .position(|p| p.name == f.decreases)
            .unwrap();
        let decl = self.kernel.data_declaration(family.id)?;
        let p = decl.parameters.len();
        let mut env = self.globals.clone();
        let mut parameters = vec![];
        for param in &f.parameters {
            let ty = self.rewrite(&param.ty, &env, None)?;
            let name = self.bind(&mut env, &param.name)?;
            parameters.push(Parameter {
                name,
                ty,
                plicity: param.plicity,
            });
        }
        let signature = pis(&parameters, self.rewrite(&f.result, &env, None)?);
        let prefix = parameters[..d]
            .iter()
            .map(|p| E::name(&p.name))
            .collect::<Vec<_>>();
        let params = family.arguments[..p]
            .iter()
            .map(|t| instantiated(&family.prefix, t.clone(), prefix.clone()))
            .collect::<Vec<_>>();
        let mut index_names = HashSet::new();
        let patterns = family.arguments[p..]
            .iter()
            .map(|t| {
                self.index_pattern(
                    t,
                    &family.prefix,
                    &prefix,
                    &f.parameters[..d],
                    &mut index_names,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let index_positions = f
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, p)| index_names.contains(&p.name))
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        let mut body = &f.body;
        let mut locals = vec![];
        let mut checked = vec![];
        while let Body::Let {
            name,
            ty,
            value,
            body: next,
        } = body.unlocated()
        {
            let local = Local {
                name: name.clone(),
                ty: ty.clone(),
                value: value.clone(),
            };
            checked.push(self.local(&local, &mut env, None)?);
            locals.push(local);
            body = next;
        }
        let Body::Match { scrutinee, arms } = body.unlocated() else {
            let Body::Return(value) = body.unlocated() else {
                unreachable!()
            };
            return Ok(lambdas(
                &parameters,
                wrap_locals(checked, self.rewrite(value, &env, None)?),
            )
            .ann(signature));
        };
        if scrutinee != &f.decreases {
            return Err(Error::UnsupportedMatch(
                "outer match must inspect decreases parameter".into(),
            ));
        }
        let mut ordered = vec![None; decl.constructors.len()];
        for arm in arms {
            let Pattern::Constructor { name, fields } = arm.pattern.unlocated() else {
                return Err(Error::InvalidPattern(
                    "expected an inductive constructor".into(),
                ));
            };
            let Some(E::Core(term)) = self.globals.get(name) else {
                return Err(Error::UnknownName(name.clone()));
            };
            let mut term = self.kernel.normalize(term)?;
            while let Term::Lam { body, .. } = term.as_ref() {
                term = body.clone();
            }
            let Term::Data {
                op: DataOp::Constructor(id, c),
                ..
            } = term.as_ref()
            else {
                return Err(Error::InvalidPattern("expected a constructor".into()));
            };
            if *id != family.id || decl.constructors[*c].fields.len() != fields.len() {
                return Err(arm.pattern.locate_error(Error::InvalidPattern(
                    "wrong family or constructor arity".into(),
                )));
            }
            if ordered[*c].replace(arm).is_some() {
                return Err(arm
                    .pattern
                    .locate_error(Error::InvalidPattern("duplicate constructor branch".into())));
            }
        }
        let indices = patterns.iter().map(|_| self.fresh()).collect::<Vec<_>>();
        let item = self.fresh();
        let pending = patterns
            .iter()
            .cloned()
            .zip(indices.iter().map(|n| Symbolic {
                expression: E::name(n),
                shape: Shape::Variable,
            }))
            .collect();
        let mut motive_env = env.clone();
        self.clear_locals(&locals, &mut motive_env);
        let failure = lambda(&item, unit_type(f.motive_level));
        let mut motive = self.index_decision(
            pending,
            motive_env,
            f.motive_level
                .checked_add(1)
                .ok_or(Error::UniverseOverflow)?,
            &mut |this, refined| {
                let mut refined = refined.clone();
                refined.insert(f.decreases.clone(), E::name(&item));
                Ok(lambda(&item, this.generalized_type(f, d, &refined)?))
            },
            &failure,
        )?;
        for index in indices.iter().rev() {
            motive = lambda(index, motive);
        }
        let history = super::data::recursive_body(body)
            && nested_match(body, false)
            && decl.constructors.iter().all(|c| {
                c.fields
                    .iter()
                    .all(|ty| !matches!(ty.as_ref(), Term::Pi { .. }))
            });
        if history {
            motive = self.history_motive(family.id, &params, &motive, f.motive_level)?;
        }
        let mut branches = vec![];
        for (c, arm) in ordered.into_iter().enumerate() {
            let ctor = &decl.constructors[c];
            let mut branch_env = env.clone();
            self.clear_locals(&locals, &mut branch_env);
            let names = arm
                .map(|arm| match arm.pattern.unlocated() {
                    Pattern::Constructor { fields, .. } => fields.clone(),
                    _ => unreachable!(),
                })
                .unwrap_or_else(|| ctor.fields.iter().map(|_| self.fresh()).collect());
            let mut bound = vec![];
            for name in &names {
                if arm.is_some() {
                    bound.push(self.bind(&mut branch_env, name)?);
                } else {
                    bound.push(name.clone());
                }
            }
            let values = params
                .iter()
                .cloned()
                .chain(bound.iter().map(E::name))
                .collect::<Vec<_>>();
            let telescope = decl
                .parameters
                .iter()
                .chain(&ctor.fields)
                .cloned()
                .collect::<Vec<_>>();
            let actual = ctor
                .indices
                .iter()
                .map(|t| self.symbolic(t, &telescope, &values))
                .collect::<Result<Vec<_>, _>>()?;
            let mut constructor = E::Core(self.kernel.data_constructor_function(family.id, c)?);
            for arg in &params {
                constructor = constructor.implicit(arg.clone());
            }
            for name in &bound {
                constructor = constructor.app(E::name(name));
            }
            branch_env.insert(f.decreases.clone(), constructor);
            let mut recursions = vec![];
            let mut histories = vec![];
            for (field, ty) in ctor.fields.iter().enumerate() {
                let mut head = ty.as_ref();
                while let Term::Pi { codomain, .. } = head {
                    head = codomain.as_ref();
                }
                if !matches!(ty.as_ref(), Term::Data { .. })
                    && matches!(head, Term::Data { op: DataOp::Type(id), .. } if *id == family.id)
                {
                    // Function-valued children have an IH even when surface
                    // structural calls cannot select them as a subterm.
                    bound.push(self.fresh());
                }
                if matches!(ty.as_ref(), Term::Data { op: DataOp::Type(id), .. } if *id == family.id)
                {
                    let ih = self.fresh();
                    bound.push(ih.clone());
                    histories.push(E::name(&ih));
                    let mut arguments = parameters
                        .iter()
                        .map(|p| Some(p.name.clone()))
                        .collect::<Vec<_>>();
                    arguments[d] = Some(bound[field].clone());
                    for arg in &mut arguments[d + 1..] {
                        *arg = None;
                    }
                    recursions.push(Recursion {
                        ih: if history {
                            E::name(&ih).fst()
                        } else {
                            E::name(&ih)
                        },
                        history: history.then(|| E::name(&ih)),
                        target: d,
                        indices: index_positions.clone(),
                        signature: Some(lambdas(&parameters, E::Zero)),
                        plicities: f.parameters.iter().map(|p| p.plicity).collect(),
                        arguments,
                        suffix: f.parameters[d + 1..].iter().map(|p| p.plicity).collect(),
                    });
                }
            }
            let mut reachable = false;
            let result = self.index_decision(
                patterns.iter().cloned().zip(actual).collect(),
                branch_env,
                f.motive_level,
                &mut |this, refined| {
                    reachable = true;
                    let arm = arm.ok_or_else(|| {
                        Error::InvalidPattern("match must cover every possible constructor".into())
                    })?;
                    let mut refined = refined.clone();
                    let mut suffix = vec![];
                    for param in &f.parameters[d + 1..] {
                        let ty = this.rewrite(&param.ty, &refined, None)?;
                        let name = this.bind(&mut refined, &param.name)?;
                        suffix.push(Parameter {
                            name,
                            ty,
                            plicity: param.plicity,
                        });
                    }
                    let replay = this.replay_locals(&locals, &mut refined, recursions.first())?;
                    let body =
                        this.data_branch(&arm.body, &mut refined, &recursions, f.motive_level)?;
                    Ok(lambdas(&suffix, wrap_locals(replay, body)))
                },
                &unit_value(f.motive_level),
            )?;
            if let Some(arm) = arm.filter(|_| !reachable) {
                return Err(arm.pattern.locate_error(Error::InvalidPattern(
                    "impossible constructor branch".into(),
                )));
            }
            let result = if history {
                E::pair(
                    result,
                    histories
                        .into_iter()
                        .rev()
                        .fold(E::Zero, |tail, head| E::pair(head, tail)),
                )
            } else {
                result
            };
            branches.push(bound.iter().rev().fold(result, |body, n| lambda(n, body)));
        }
        let result = E::Induct {
            level: f.motive_level,
            value: Box::new(env[&f.decreases].clone()),
            motive: Box::new(motive),
            branches,
        };
        let result = if history { result.fst() } else { result };
        let result = parameters[d + 1..]
            .iter()
            .fold(result, |f, p| apply(f, E::name(&p.name), p.plicity));
        Ok(lambdas(&parameters, wrap_locals(checked, result)).ann(signature))
    }
}
