use super::*;
use deppy_core::{DataOp, Term, Tm};

pub(super) struct Family {
    pub id: u64,
    pub arguments: Vec<Tm>,
    pub prefix: Vec<Tm>,
}
/// Reuse structural index specialization for a type-directed nested case.
/// All free locals have been lambda-lifted by the elaborator.
pub(crate) fn lifted_cases(
    kernel: deppy_core::Kernel,
    remaining: &mut usize,
    globals: HashMap<String, E>,
    mut function: Function,
    id: u64,
    arguments: Vec<Tm>,
    prefix: Vec<Tm>,
) -> Result<E, Error> {
    let mut lower = Lowerer {
        generated: true,
        kernel,
        remaining: *remaining,
        next: 0,
        family: None,
        alternatives: vec![],
        globals,
    };
    if let Body::Match { arms, .. } = &mut function.body {
        for arm in arms {
            let mut env = lower.globals.clone();
            for parameter in &function.parameters {
                env.insert(parameter.name.clone(), E::name(&parameter.name));
            }
            if let Pattern::Constructor { fields, .. } = arm.pattern.unlocated() {
                for field in fields {
                    env.insert(field.clone(), E::name(field));
                }
            }
            if let Body::Return(body) = &mut arm.body {
                *body = lower.rewrite(body, &env, None)?;
            }
        }
    }
    let result = lower.data_function(
        &function,
        Family {
            id,
            arguments,
            prefix,
        },
    );
    *remaining = lower.remaining;
    result
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
pub(super) fn instantiated(types: &[Tm], term: Tm, args: impl IntoIterator<Item = E>) -> E {
    args.into_iter()
        .fold(E::Core(close(types, term)), |f, arg| f.app(arg))
}
pub(super) fn nested_match(body: &Body, inside: bool) -> bool {
    match body.unlocated() {
        Body::Match { arms, .. } => inside || arms.iter().any(|arm| nested_match(&arm.body, true)),
        Body::Let { body, .. } => nested_match(body, inside),
        _ => false,
    }
}
pub(super) fn recursive_body(body: &Body) -> bool {
    match body.unlocated() {
        Body::Return(e) => e.contains_recur(),
        Body::Let { value, body, .. } => value.contains_recur() || recursive_body(body),
        Body::Match { arms, .. } => arms.iter().any(|arm| recursive_body(&arm.body)),
        Body::Located { .. } => unreachable!(),
    }
}
impl Lowerer {
    // A course-of-values history is derived using ordinary induction into Type:
    // Hist(P, C(fields)) = P(C(fields)) × Hist(child1) × ... × Nat.
    // The terminal Nat is inhabited by zero and is only the empty product.
    pub(super) fn history_motive(
        &mut self,
        family: u64,
        params: &[E],
        motive: &E,
        level: u32,
    ) -> Result<E, Error> {
        let decl = self.kernel.data_declaration(family)?;
        let indices = decl
            .indices
            .iter()
            .map(|_| self.fresh())
            .collect::<Vec<_>>();
        let item = self.fresh();
        let mut family_type = E::Core(self.kernel.data_type_function(family)?);
        for param in params {
            family_type = family_type.implicit(param.clone());
        }
        for index in &indices {
            family_type = family_type.app(E::name(index));
        }
        let mut motive_type = E::pi(&item, Plicity::Explicit, family_type, E::Universe(level));
        for i in (0..indices.len()).rev() {
            let telescope = decl
                .parameters
                .iter()
                .chain(&decl.indices[..i])
                .cloned()
                .collect::<Vec<_>>();
            let args = params
                .iter()
                .cloned()
                .chain(indices[..i].iter().map(E::name));
            let domain = instantiated(&telescope, decl.indices[i].clone(), args);
            motive_type = E::pi(&indices[i], Plicity::Explicit, domain, motive_type);
        }
        let motive = motive.clone().ann(motive_type);
        let mut universe = lambda(&item, E::Universe(level));
        for index in indices.iter().rev() {
            universe = lambda(index, universe);
        }
        let mut branches = vec![];
        for ctor in &decl.constructors {
            let fields = ctor.fields.iter().map(|_| self.fresh()).collect::<Vec<_>>();
            let mut bound = fields.clone();
            let mut histories = vec![];
            for (field, ty) in ctor.fields.iter().enumerate() {
                if let Term::Data {
                    op: DataOp::Type(id),
                    arguments,
                } = ty.as_ref()
                {
                    if *id != family {
                        continue;
                    }
                    let ih = self.fresh();
                    let telescope = decl
                        .parameters
                        .iter()
                        .chain(&ctor.fields[..field])
                        .cloned()
                        .collect::<Vec<_>>();
                    let args = params
                        .iter()
                        .cloned()
                        .chain(fields[..field].iter().map(E::name))
                        .collect::<Vec<_>>();
                    let mut result = motive.clone();
                    for index in &arguments[params.len()..] {
                        result = result.app(instantiated(&telescope, index.clone(), args.clone()));
                    }
                    result = result.app(E::name(&fields[field]));
                    histories.push(E::sigma(self.fresh(), result, E::name(&ih)));
                    bound.push(ih);
                }
            }
            let mut product = E::Nat;
            for history in histories.into_iter().rev() {
                product = E::sigma(self.fresh(), history, product);
            }
            branches.push(
                bound
                    .iter()
                    .rev()
                    .fold(product, |body, name| lambda(name, body)),
            );
        }
        let mut result = E::Induct {
            level: level.checked_add(1).ok_or(Error::UniverseOverflow)?,
            value: Box::new(E::name(&item)),
            motive: Box::new(universe),
            branches,
        };
        let mut current = motive.clone();
        for index in &indices {
            current = current.app(E::name(index));
        }
        current = current.app(E::name(&item));
        result = E::sigma(self.fresh(), current, result);
        result = lambda(&item, result);
        for index in indices.iter().rev() {
            result = lambda(index, result);
        }
        Ok(result)
    }
    pub(super) fn data_function(&mut self, f: &Function, family: Family) -> Result<E, Error> {
        let d = f
            .parameters
            .iter()
            .position(|p| p.name == f.decreases)
            .unwrap();
        let decl = self.kernel.data_declaration(family.id)?.clone();
        if family.arguments[decl.parameters.len()..]
            .iter()
            .any(|index| !matches!(index.as_ref(), Term::Var(_)))
        {
            return self.specialized_data_function(f, family);
        }
        let history = recursive_body(&f.body)
            && nested_match(&f.body, false)
            && decl.constructors.iter().all(|c| {
                c.fields
                    .iter()
                    .all(|ty| !matches!(ty.as_ref(), Term::Pi { .. }))
            });
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
            if history {
                motive = self.history_motive(family.id, &param_values, &motive, f.motive_level)?;
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
                let mut histories = vec![];
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
                        histories.push(E::name(&ih));
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
                                ih: if history {
                                    E::name(&ih).fst()
                                } else {
                                    E::name(&ih)
                                },
                                history: history.then(|| E::name(&ih)),
                                target: d,
                                indices: indices.clone(),
                                signature: Some(lambdas(&parameters, E::Zero)),
                                plicities: f.parameters.iter().map(|p| p.plicity).collect(),
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
                let branch =
                    self.data_branch(&arm.body, &mut branch_env, &recursions, f.motive_level)?;
                let branch = lambdas(&suffix, wrap_locals(replay, branch));
                let branch = if history {
                    let product = histories
                        .into_iter()
                        .rev()
                        .fold(E::Zero, |tail, head| E::pair(head, tail));
                    E::pair(branch, product)
                } else {
                    branch
                };
                branches.push(bound.iter().rev().fold(branch, |b, n| lambda(n, b)));
            }
            let elim = E::Induct {
                level: f.motive_level,
                value: Box::new(env[&f.decreases].clone()),
                motive: Box::new(motive),
                branches,
            };
            let elim = if history { elim.fst() } else { elim };
            Ok(parameters[d + 1..]
                .iter()
                .fold(elim, |f, p| apply(f, E::name(&p.name), p.plicity)))
        })()
        .map_err(|error| body.locate_error(error))?;
        Ok(lambdas(&parameters, wrap_locals(checked, result)).ann(signature))
    }
    pub(super) fn data_branch(
        &mut self,
        body: &Body,
        env: &mut Env,
        recursions: &[Recursion],
        level: u32,
    ) -> Result<E, Error> {
        match body {
            Body::Located { location, body } => self
                .data_branch(body, env, recursions, level)
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
                    self.data_branch(body, env, recursions, level)?,
                ))
            }
            Body::Match { scrutinee, arms } => {
                let value = env
                    .get(scrutinee)
                    .cloned()
                    .ok_or_else(|| Error::UnknownName(scrutinee.clone()))?;
                let parent = recursions.iter().find(|rec| matches!(value.unlocated(), E::Name(name) if rec.arguments[rec.target].as_ref() == Some(name)) && rec.history.is_some()).cloned();
                let generalized = parent
                    .as_ref()
                    .map(|rec| (self.fresh(), rec.history.clone().unwrap()));
                let mut branches = vec![];
                for arm in arms {
                    let Pattern::Constructor { name, fields } = arm.pattern.unlocated() else {
                        return Err(arm.pattern.locate_error(Error::InvalidPattern(
                            "expected an inductive constructor".into(),
                        )));
                    };
                    let mut inner = env.clone();
                    let mut seen = HashSet::new();
                    let mut bound = vec![];
                    for field in fields {
                        if env.contains_key(field) || !seen.insert(field) {
                            return Err(arm.pattern.locate_error(Error::InvalidPattern(
                                "pattern shadows or repeats a binding".into(),
                            )));
                        }
                        bound.push(self.bind(&mut inner, field)?);
                    }
                    let mut recursions = recursions.to_vec();
                    if let (Some(parent), Some((history, _))) = (&parent, &generalized) {
                        let Some(E::Core(constructor)) = self.globals.get(name) else {
                            return Err(Error::UnknownName(name.clone()));
                        };
                        let mut constructor = self.kernel.normalize(constructor)?;
                        while let Term::Lam { body, .. } = constructor.as_ref() {
                            constructor = body.clone();
                        }
                        let Term::Data {
                            op: DataOp::Constructor(id, c),
                            ..
                        } = constructor.as_ref()
                        else {
                            return Err(Error::ExpectedInductive);
                        };
                        let decl = self.kernel.data_declaration(*id)?;
                        let mut product = E::name(history).snd();
                        for rec in &mut recursions {
                            if rec.arguments == parent.arguments {
                                rec.ih = E::name(history).fst();
                                rec.history = Some(E::name(history));
                            }
                        }
                        for (field, ty) in decl.constructors[*c].fields.iter().enumerate() {
                            if let Term::Data {
                                op: DataOp::Type(other),
                                arguments,
                            } = ty.as_ref()
                            {
                                if other != id {
                                    continue;
                                }
                                let mut child = parent.clone();
                                child.arguments[child.target] = Some(bound[field].clone());
                                for (index, arg) in child
                                    .indices
                                    .iter()
                                    .zip(&arguments[decl.parameters.len()..])
                                {
                                    let Term::Var(v) = arg.as_ref() else {
                                        return Err(Error::UnsupportedMatch(
                                            "recursive index must be a constructor field".into(),
                                        ));
                                    };
                                    if *v >= field {
                                        return Err(Error::UnsupportedMatch(
                                            "recursive index must precede its field".into(),
                                        ));
                                    }
                                    child.arguments[*index] = Some(bound[field - 1 - v].clone());
                                }
                                child.history = Some(product.clone().fst());
                                child.ih = product.clone().fst().fst();
                                recursions.push(child);
                                product = product.snd();
                            }
                        }
                    }
                    let body = self.data_branch(&arm.body, &mut inner, &recursions, level)?;
                    let location = match &arm.pattern {
                        Pattern::Located { location, .. } => Some(location.clone()),
                        _ => None,
                    };
                    branches.push(crate::CaseBranch {
                        constructor: name.clone().into(),
                        fields: bound,
                        body,
                        location,
                    });
                }
                Ok(E::Cases {
                    level,
                    value: Box::new(value),
                    branches,
                    generalize: generalized.into_iter().collect(),
                })
            }
        }
    }
    fn data_rewrite(&mut self, expr: &E, env: &Env, recursions: &[Recursion]) -> Result<E, Error> {
        let previous = std::mem::replace(&mut self.alternatives, recursions.to_vec());
        let result = self.rewrite(expr, env, None);
        self.alternatives = previous;
        result
    }
}
