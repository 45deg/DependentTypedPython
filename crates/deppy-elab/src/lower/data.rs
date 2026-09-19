use super::*;
use deppy_core::{DataOp, Term, Tm};

pub(super) struct Family {
    pub id: u64,
    pub arguments: Vec<Tm>,
    pub prefix: Vec<Tm>,
}
fn close(types: &[Tm], mut term: Tm) -> Tm {
    for ty in types.iter().rev() {
        term = Term::Lam {
            relevance: deppy_core::Relevance::Runtime,
            domain: ty.clone(),
            body: term,
        }
        .arc();
    }
    term
}
fn instantiated(types: &[Tm], term: Tm, args: impl IntoIterator<Item = E>) -> E {
    args.into_iter()
        .fold(E::Core(close(types, term)), |f, arg| f.app(arg))
}
impl Lowerer {
    pub(super) fn data_function(&mut self, f: &Function, family: Family) -> Result<E, Error> {
        let d = f
            .parameters
            .iter()
            .position(|p| p.name == f.decreases)
            .unwrap();
        let decl = self.kernel.data_declaration(family.id)?.clone();
        let p = decl.parameters.len();
        let mut env = self.globals.clone();
        let mut parameters = vec![];
        let mut names = HashSet::new();
        for param in &f.parameters {
            if !names.insert(&param.name) {
                return Err(Error::InvalidDeclarationName(param.name.clone()));
            }
            let ty = self.rewrite(&param.ty, &env, None)?;
            let name = self.bind(&mut env, &param.name)?;
            parameters.push(Parameter {
                name,
                plicity: param.plicity,
                ty,
            });
        }
        let signature = pis(&parameters, self.rewrite(&f.result, &env, None)?);
        let mut indices = vec![];
        for index in &family.arguments[p..] {
            let Term::Var(index) = index.as_ref() else {
                return Err(Error::UnsupportedMatch(
                    "structural indexed match requires distinct earlier index parameters".into(),
                ));
            };
            if *index >= d || indices.contains(&(d - 1 - index)) {
                return Err(Error::UnsupportedMatch(
                    "structural indexed match requires distinct earlier index parameters".into(),
                ));
            }
            indices.push(d - 1 - index);
        }
        let param_values = family.arguments[..p]
            .iter()
            .map(|ty| {
                instantiated(
                    &family.prefix,
                    ty.clone(),
                    parameters[..d].iter().map(|p| E::name(&p.name)),
                )
            })
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
        let result = (|| {
            let Body::Match { scrutinee, arms } = body.unlocated() else {
                if let Body::Return(value) = body.unlocated() {
                    return self.rewrite(value, &env, None);
                }
                unreachable!()
            };
            if scrutinee != &f.decreases {
                return Err(Error::UnsupportedMatch(
                    "outer match must inspect decreases parameter".into(),
                ));
            }
            let mut ordered = vec![None; decl.constructors.len()];
            for arm in arms {
                let Pattern::Constructor { name, fields } = arm.pattern.unlocated() else {
                    return Err(arm.pattern.locate_error(Error::InvalidPattern(
                        "expected a constructor of the inductive family".into(),
                    )));
                };
                let Some(E::Core(function)) = self.globals.get(name) else {
                    return Err(arm.pattern.locate_error(Error::UnknownName(name.clone())));
                };
                let mut term = self.kernel.normalize(function)?;
                while let Term::Lam { body, .. } = term.as_ref() {
                    term = body.clone();
                }
                let Term::Data {
                    op: DataOp::Constructor(id, c),
                    ..
                } = term.as_ref()
                else {
                    return Err(arm
                        .pattern
                        .locate_error(Error::InvalidPattern("expected a constructor".into())));
                };
                if *id != family.id || fields.len() != decl.constructors[*c].fields.len() {
                    return Err(arm.pattern.locate_error(Error::InvalidPattern(
                        "wrong family or constructor arity".into(),
                    )));
                }
                if ordered[*c].replace(arm).is_some() {
                    return Err(arm.pattern.locate_error(Error::InvalidPattern(
                        "duplicate constructor branch".into(),
                    )));
                }
            }
            if ordered.iter().any(Option::is_none) {
                return Err(Error::InvalidPattern(
                    "match must cover every constructor".into(),
                ));
            }
            let index_names = indices.iter().map(|_| self.fresh()).collect::<Vec<_>>();
            let item = self.fresh();
            let mut motive_env = env.clone();
            self.clear_locals(&locals, &mut motive_env);
            for (index, name) in indices.iter().zip(&index_names) {
                motive_env.insert(f.parameters[*index].name.clone(), E::name(name));
            }
            motive_env.insert(f.decreases.clone(), E::name(&item));
            let mut motive = lambda(&item, self.generalized_type(f, d, &motive_env)?);
            for name in index_names.iter().rev() {
                motive = lambda(name, motive);
            }
            let mut branches = vec![];
            for (c, arm) in ordered.into_iter().enumerate() {
                let arm = arm.unwrap();
                let Pattern::Constructor { fields, .. } = arm.pattern.unlocated() else {
                    unreachable!()
                };
                let ctor = &decl.constructors[c];
                let mut branch_env = env.clone();
                self.clear_locals(&locals, &mut branch_env);
                let mut bound = vec![];
                let mut seen = HashSet::new();
                for field in fields {
                    if env.contains_key(field) || !seen.insert(field) {
                        return Err(arm.pattern.locate_error(Error::InvalidPattern(
                            "pattern shadows or repeats a binding".into(),
                        )));
                    }
                    bound.push(self.bind(&mut branch_env, field)?);
                }
                let field_values = bound.iter().map(E::name).collect::<Vec<_>>();
                let args = param_values
                    .iter()
                    .cloned()
                    .chain(field_values.iter().cloned())
                    .collect::<Vec<_>>();
                let telescope = decl
                    .parameters
                    .iter()
                    .chain(&ctor.fields)
                    .cloned()
                    .collect::<Vec<_>>();
                let mut constructor = E::Core(self.kernel.data_constructor_function(family.id, c)?);
                for arg in &param_values {
                    constructor = constructor.implicit(arg.clone());
                }
                for arg in &field_values {
                    constructor = constructor.app(arg.clone());
                }
                branch_env.insert(f.decreases.clone(), constructor);
                for (index, result) in indices.iter().zip(&ctor.indices) {
                    branch_env.insert(
                        f.parameters[*index].name.clone(),
                        instantiated(&telescope, result.clone(), args.clone()),
                    );
                }
                let mut recursions = vec![];
                for (field, ty) in ctor.fields.iter().enumerate() {
                    // The kernel has already checked positivity. Direct recursive
                    // fields become legal recursive targets; function-valued fields
                    // receive IHs but require explicit induct for recursive calls.
                    let mut tail = ty.as_ref();
                    while let Term::Pi { codomain, .. } = tail {
                        tail = codomain.as_ref();
                    }
                    if matches!(tail, Term::Data { op: DataOp::Type(id), .. } if *id == family.id) {
                        let ih = self.fresh();
                        bound.push(ih.clone());
                        if let Term::Data {
                            op: DataOp::Type(_),
                            arguments,
                        } = ty.as_ref()
                        {
                            let mut arguments_expected = parameters
                                .iter()
                                .take(d + 1)
                                .map(|p| Some(p.name.clone()))
                                .collect::<Vec<_>>();
                            arguments_expected[d] = Some(bound[field].clone());
                            for (index, argument) in indices.iter().zip(&arguments[p..]) {
                                let Term::Var(v) = argument.as_ref() else {
                                    return Err(Error::UnsupportedMatch(
                                        "recursive indices must be constructor fields".into(),
                                    ));
                                };
                                if *v >= field {
                                    return Err(Error::UnsupportedMatch(
                                        "recursive index must precede the recursive field".into(),
                                    ));
                                }
                                arguments_expected[*index] = Some(bound[field - 1 - v].clone());
                            }
                            arguments_expected.extend(f.parameters[d + 1..].iter().map(|_| None));
                            recursions.push(Recursion {
                                ih,
                                arguments: arguments_expected,
                                suffix: f.parameters[d + 1..].iter().map(|p| p.plicity).collect(),
                            });
                        }
                    }
                }
                let mut suffix = vec![];
                for param in &f.parameters[d + 1..] {
                    let ty = self.rewrite(&param.ty, &branch_env, None)?;
                    let name = self.bind(&mut branch_env, &param.name)?;
                    suffix.push(Parameter {
                        name,
                        ty,
                        plicity: param.plicity,
                    });
                }
                // Prefix lets are checked before splitting and replayed with refined indices.
                let replay = self.replay_locals(&locals, &mut branch_env, recursions.first())?;
                let branch = self.data_branch(&arm.body, &mut branch_env, &recursions)?;
                let branch = lambdas(&suffix, wrap_locals(replay, branch));
                branches.push(bound.iter().rev().fold(branch, |b, n| lambda(n, b)));
            }
            let elim = E::Induct {
                level: f.motive_level,
                value: Box::new(env[&f.decreases].clone()),
                motive: Box::new(motive),
                branches,
            };
            Ok(parameters[d + 1..]
                .iter()
                .fold(elim, |f, p| apply(f, E::name(&p.name), p.plicity)))
        })()
        .map_err(|error| body.locate_error(error))?;
        Ok(lambdas(&parameters, wrap_locals(checked, result)).ann(signature))
    }
    fn data_branch(
        &mut self,
        body: &Body,
        env: &mut Env,
        recursions: &[Recursion],
    ) -> Result<E, Error> {
        match body {
            Body::Located { location, body } => self
                .data_branch(body, env, recursions)
                .map_err(|e| e.at(location)),
            Body::Return(value) => self.data_rewrite(value, env, recursions),
            Body::Let {
                name,
                ty,
                value,
                body,
            } => {
                let ty = ty
                    .as_ref()
                    .map(|ty| self.data_rewrite(ty, env, recursions))
                    .transpose()?;
                let value = self.data_rewrite(value, env, recursions)?;
                let name = self.bind(env, name)?;
                Ok(E::let_in(
                    name,
                    ty,
                    value,
                    self.data_branch(body, env, recursions)?,
                ))
            }
            Body::Match { .. } => Err(Error::UnsupportedMatch(
                "nested general matches require an explicit induct".into(),
            )),
        }
    }
    fn data_rewrite(&mut self, expr: &E, env: &Env, recursions: &[Recursion]) -> Result<E, Error> {
        let previous = std::mem::replace(&mut self.alternatives, recursions.to_vec());
        let result = self.rewrite(expr, env, None);
        self.alternatives = previous;
        result
    }
}
