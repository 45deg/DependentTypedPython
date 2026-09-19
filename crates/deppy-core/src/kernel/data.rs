use super::*;
use crate::{DataDecl, DataOp, Relevance};
use value::Closure;

type ResultType = Arc<dyn Fn(&Env, &mut Budget) -> Result<Val, Error> + Send + Sync>;

fn nominal(id: u64, arguments: Vec<Val>) -> Val {
    Arc::new(Value::Data {
        op: DataOp::Type(id),
        arguments,
    })
}
fn apps(
    mut f: Val,
    args: impl IntoIterator<Item = Val>,
    budget: &mut Budget,
) -> Result<Val, Error> {
    for argument in args {
        f = value::apply(&f, argument, budget)?;
    }
    Ok(f)
}
/// Build a dependent telescope without quoting open semantic variables.
fn telescope(
    types: Arc<Vec<Tm>>,
    position: usize,
    env: Env,
    end: ResultType,
    budget: &mut Budget,
) -> Result<Val, Error> {
    budget.tick()?;
    if position == types.len() {
        return end(&env, budget);
    }
    let domain = value::eval(&types[position], &env, budget)?;
    Ok(Arc::new(Value::Pi(
        Relevance::Runtime,
        domain,
        Closure::Native(Arc::new(move |arg, budget| {
            let mut env = env.clone();
            env.push(arg);
            telescope(types.clone(), position + 1, env, end.clone(), budget)
        })),
    )))
}
fn check_arguments(
    ctx: &Context,
    types: &[Tm],
    arguments: &[Tm],
    mut env: Env,
    budget: &mut Budget,
) -> Result<Env, Error> {
    if types.len() != arguments.len() {
        return Err(Error::ArityMismatch);
    }
    for (ty, arg) in types.iter().zip(arguments) {
        let ty = value::eval(ty, &env, budget)?;
        check(ctx, arg, &ty, budget)?;
        env.push(value::eval(arg, &ctx.env, budget)?);
    }
    Ok(env)
}
pub(super) fn declaration(id: u64, budget: &mut Budget) -> Result<DataDecl, Error> {
    if let Some(decl) = budget.2.get(&id) {
        return Ok(decl.clone());
    }
    let level = crate::standard::vector_level(id).ok_or(Error::UnknownInductive(id))?;
    let decl = crate::standard::vector_declaration(level);
    let mut kernel = Kernel {
        definitions: budget.1.clone(),
        data: budget.2.clone(),
        globals: Arc::default(),
        max_steps: budget.0,
    };
    kernel.declare_data(id, decl.clone())?;
    budget.2 = kernel.data;
    Ok(decl)
}

impl Kernel {
    pub fn data_declaration(&self, id: u64) -> Result<DataDecl, Error> {
        declaration(
            id,
            &mut Budget(self.max_steps, self.definitions.clone(), self.data.clone()),
        )
    }
    /// Atomically register a strictly positive family. Recursive parameters must
    /// remain uniform; recursive occurrences under arbitrary type operators are rejected.
    pub fn declare_data(&mut self, id: u64, decl: DataDecl) -> Result<(), Error> {
        if let Some(level) = crate::standard::vector_level(id) {
            if decl != crate::standard::vector_declaration(level) {
                return Err(Error::DuplicateInductive(id));
            }
        }
        if self.data.contains_key(&id) {
            return Err(Error::DuplicateInductive(id));
        }
        decl.level.checked_add(1).ok_or(Error::UniverseOverflow)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        budget.tick()?;
        let mut ctx = self.context();
        for ty in &decl.parameters {
            universe(&ctx, ty, &mut budget)?;
            ctx = ctx.bind(value::eval(ty, &ctx.env, &mut budget)?);
        }
        let params = ctx.env.clone();
        let mut indices_ctx = ctx.clone();
        for ty in &decl.indices {
            universe(&indices_ctx, ty, &mut budget)?;
            indices_ctx = indices_ctx.bind(value::eval(ty, &indices_ctx.env, &mut budget)?);
        }
        Arc::make_mut(&mut budget.2).insert(id, decl.clone());
        for ctor in &decl.constructors {
            budget.tick()?;
            let mut ctx = ctx.clone();
            for ty in &ctor.fields {
                reject_recursive_operations(ty, id, &mut budget)?;
                if universe(&ctx, ty, &mut budget)? > decl.level {
                    return Err(Error::FieldUniverseTooLarge);
                }
                let ty = value::eval(ty, &ctx.env, &mut budget)?;
                positive(&ty, id, &params, ctx.env.len(), &mut budget)?;
                ctx = ctx.bind(ty);
            }
            for index in &ctor.indices {
                reject_recursive_operations(index, id, &mut budget)?;
            }
            let result = check_arguments(
                &ctx,
                &decl.indices,
                &ctor.indices,
                params.clone(),
                &mut budget,
            )?;
            for index in &result[params.len()..] {
                let index = value::quote(index, ctx.env.len(), &mut budget)?;
                if contains(&index, id, &mut budget)? {
                    return Err(Error::InvalidPositivity);
                }
            }
        }
        Arc::make_mut(&mut self.data).insert(id, decl);
        Ok(())
    }
}

pub(super) fn synth_data(
    ctx: &Context,
    op: DataOp,
    arguments: &[Tm],
    budget: &mut Budget,
) -> Result<Val, Error> {
    let id = op.id();
    let decl = declaration(id, budget)?;
    let p = decl.parameters.len();
    if arguments.len() < p {
        return Err(Error::ArityMismatch);
    }
    let params = check_arguments(ctx, &decl.parameters, &arguments[..p], vec![], budget)?;
    let rest = &arguments[p..];
    match op {
        DataOp::Absurd(_) => {
            let i = decl.indices.len();
            if rest.len() != i + 2 {
                return Err(Error::ArityMismatch);
            }
            let type_args =
                check_arguments(ctx, &decl.indices, &rest[..i], params.clone(), budget)?;
            universe(ctx, &rest[i], budget)?;
            check(ctx, &rest[i + 1], &nominal(id, type_args.clone()), budget)?;
            for ctor in &decl.constructors {
                let mut env = params.clone();
                for f in 0..ctor.fields.len() {
                    env.push(value::fresh(ctx.env.len() + f));
                }
                let mut impossible = false;
                for (index, actual) in ctor.indices.iter().zip(&type_args[p..]) {
                    let index = value::eval(index, &env, budget)?;
                    impossible |= disjoint(&index, actual, budget)?;
                }
                if !impossible {
                    return Err(Error::ExpectedEmptyInductive);
                }
            }
            value::eval(&rest[i], &ctx.env, budget)
        }
        DataOp::Type(_) => {
            check_arguments(ctx, &decl.indices, rest, params, budget)?;
            Ok(Arc::new(Value::Universe(decl.level)))
        }
        DataOp::Constructor(_, c) => {
            let ctor = decl.constructors.get(c).ok_or(Error::ArityMismatch)?;
            let env = check_arguments(ctx, &ctor.fields, rest, params.clone(), budget)?;
            let mut args = params;
            for index in &ctor.indices {
                args.push(value::eval(index, &env, budget)?);
            }
            Ok(nominal(id, args))
        }
        DataOp::Eliminate(_, level) => {
            level.checked_add(1).ok_or(Error::UniverseOverflow)?;
            let i = decl.indices.len();
            if rest.len() != i + decl.constructors.len() + 2 {
                return Err(Error::ArityMismatch);
            }
            let type_args =
                check_arguments(ctx, &decl.indices, &rest[..i], params.clone(), budget)?;
            let motive_ty = telescope(
                Arc::new(decl.indices.clone()),
                0,
                params.clone(),
                Arc::new(move |env, _| {
                    Ok(Arc::new(Value::Pi(
                        Relevance::Runtime,
                        nominal(id, env.clone()),
                        Closure::Native(Arc::new(move |_, _| Ok(Arc::new(Value::Universe(level))))),
                    )))
                }),
                budget,
            )?;
            check(ctx, &rest[i], &motive_ty, budget)?;
            let motive = value::eval(&rest[i], &ctx.env, budget)?;
            for (c, branch) in rest[i + 1..rest.len() - 1].iter().enumerate() {
                let branch_ty = branch_type(id, c, &decl, params.clone(), motive.clone(), budget)?;
                check(ctx, branch, &branch_ty, budget)?;
            }
            let scrutinee = rest.last().unwrap();
            check(ctx, scrutinee, &nominal(id, type_args.clone()), budget)?;
            let indices = type_args[p..].to_vec();
            apps(
                motive,
                indices
                    .into_iter()
                    .chain([value::eval(scrutinee, &ctx.env, budget)?]),
                budget,
            )
        }
    }
}

fn branch_type(
    id: u64,
    c: usize,
    decl: &DataDecl,
    params: Env,
    motive: Val,
    budget: &mut Budget,
) -> Result<Val, Error> {
    let ctor = decl.constructors[c].clone();
    let p = params.len();
    let fields = Arc::new(ctor.fields.clone());
    telescope(
        fields,
        0,
        params,
        Arc::new(move |env, budget| {
            let mut hypotheses = vec![];
            for (f, ty) in ctor.fields.iter().enumerate() {
                let ty = value::eval(ty, &env[..p + f].to_vec(), budget)?;
                if let Some(ty) =
                    hypothesis_type(id, ty, env[p + f].clone(), motive.clone(), budget)?
                {
                    hypotheses.push(ty);
                }
            }
            let indices = ctor
                .indices
                .iter()
                .map(|i| value::eval(i, env, budget))
                .collect::<Result<Vec<_>, _>>()?;
            let constructor = Arc::new(Value::Data {
                op: DataOp::Constructor(id, c),
                arguments: env.clone(),
            });
            let mut result = apps(
                motive.clone(),
                indices.into_iter().chain([constructor]),
                budget,
            )?;
            for ty in hypotheses.into_iter().rev() {
                let tail = result;
                result = Arc::new(Value::Pi(
                    Relevance::Runtime,
                    ty,
                    Closure::Native(Arc::new(move |_, _| Ok(tail.clone()))),
                ));
            }
            Ok(result)
        }),
        budget,
    )
}

fn hypothesis_type(
    id: u64,
    ty: Val,
    field: Val,
    motive: Val,
    budget: &mut Budget,
) -> Result<Option<Val>, Error> {
    budget.tick()?;
    match ty.as_ref() {
        Value::Data {
            op: DataOp::Type(other),
            arguments,
        } if *other == id => {
            let p = declaration(id, budget)?.parameters.len();
            Ok(Some(apps(
                motive,
                arguments[p..].iter().cloned().chain([field]),
                budget,
            )?))
        }
        Value::Pi(relevance, domain, body) => {
            // Declaration validation permits self only in the terminal codomain.
            // A fresh probe determines whether this field is recursive.
            let probe = body.apply(value::fresh(0), budget)?;
            if !recursive_head(id, &probe, budget)? {
                return Ok(None);
            }
            let body = body.clone();
            Ok(Some(Arc::new(Value::Pi(
                *relevance,
                domain.clone(),
                Closure::Native(Arc::new(move |arg, budget| {
                    let ty = body.apply(arg.clone(), budget)?;
                    let field = value::apply(&field, arg, budget)?;
                    hypothesis_type(id, ty, field, motive.clone(), budget)?
                        .ok_or(Error::InvalidPositivity)
                })),
            ))))
        }
        _ => Ok(None),
    }
}
fn recursive_head(id: u64, ty: &Val, budget: &mut Budget) -> Result<bool, Error> {
    budget.tick()?;
    match ty.as_ref() {
        Value::Data {
            op: DataOp::Type(other),
            ..
        } => Ok(id == *other),
        Value::Pi(_, _, body) => recursive_head(id, &body.apply(value::fresh(0), budget)?, budget),
        _ => Ok(false),
    }
}

pub(crate) fn evaluate(op: DataOp, arguments: Vec<Val>, budget: &mut Budget) -> Result<Val, Error> {
    budget.tick()?;
    let DataOp::Eliminate(id, level) = op else {
        return Ok(Arc::new(if matches!(op, DataOp::Absurd(_)) {
            Value::Neutral(value::Neutral::Data { op, arguments })
        } else {
            Value::Data { op, arguments }
        }));
    };
    let decl = declaration(id, budget)?;
    let p = decl.parameters.len();
    let i = decl.indices.len();
    if arguments.len() != p + i + decl.constructors.len() + 2 {
        return Err(Error::ArityMismatch);
    }
    let scrutinee = arguments.last().unwrap();
    let Value::Data {
        op: DataOp::Constructor(other, c),
        arguments: fields,
    } = scrutinee.as_ref()
    else {
        return Ok(Arc::new(Value::Neutral(value::Neutral::Data {
            op,
            arguments,
        })));
    };
    if id != *other {
        return Err(Error::UnknownInductive(*other));
    }
    let ctor = decl.constructors.get(*c).ok_or(Error::ArityMismatch)?;
    if fields.len() != p + ctor.fields.len() {
        return Err(Error::ArityMismatch);
    }
    let motive = arguments[p + i].clone();
    let branches = arguments[p + i + 1..arguments.len() - 1].to_vec();
    let mut result = apps(branches[*c].clone(), fields[p..].iter().cloned(), budget)?;
    for (f, ty) in ctor.fields.iter().enumerate() {
        let ty = value::eval(ty, &fields[..p + f].to_vec(), budget)?;
        if recursive_head(id, &ty, budget)? {
            let ih = hypothesis(
                id,
                level,
                ty,
                fields[p + f].clone(),
                motive.clone(),
                branches.clone(),
                budget,
            )?;
            result = value::apply(&result, ih, budget)?;
        }
    }
    Ok(result)
}
fn hypothesis(
    id: u64,
    level: u32,
    ty: Val,
    field: Val,
    motive: Val,
    branches: Vec<Val>,
    budget: &mut Budget,
) -> Result<Val, Error> {
    budget.tick()?;
    match ty.as_ref() {
        Value::Data {
            op: DataOp::Type(other),
            arguments,
        } if *other == id => {
            let mut args = arguments.clone();
            args.push(motive);
            args.extend(branches);
            args.push(field);
            evaluate(DataOp::Eliminate(id, level), args, budget)
        }
        Value::Pi(relevance, domain, body) => {
            let body = body.clone();
            Ok(Arc::new(Value::Lam(
                *relevance,
                domain.clone(),
                Closure::Native(Arc::new(move |arg, budget| {
                    let ty = body.apply(arg.clone(), budget)?;
                    let field = value::apply(&field, arg, budget)?;
                    hypothesis(
                        id,
                        level,
                        ty,
                        field,
                        motive.clone(),
                        branches.clone(),
                        budget,
                    )
                })),
            )))
        }
        _ => Err(Error::InvalidPositivity),
    }
}

fn positive(
    ty: &Val,
    id: u64,
    params: &[Val],
    depth: usize,
    budget: &mut Budget,
) -> Result<(), Error> {
    budget.tick()?;
    match ty.as_ref() {
        Value::Data {
            op: DataOp::Type(other),
            arguments,
        } if *other == id => {
            if arguments.len() < params.len() {
                return Err(Error::ArityMismatch);
            }
            for (a, b) in arguments.iter().zip(params) {
                if !value::equal(a, b, depth, budget)? {
                    return Err(Error::InvalidPositivity);
                }
            }
            for argument in arguments {
                if contains(&value::quote(argument, depth, budget)?, id, budget)? {
                    return Err(Error::InvalidPositivity);
                }
            }
            Ok(())
        }
        Value::Pi(_, domain, body) => {
            if contains(&value::quote(domain, depth, budget)?, id, budget)? {
                return Err(Error::InvalidPositivity);
            }
            positive(
                &body.apply(value::fresh(depth), budget)?,
                id,
                params,
                depth + 1,
                budget,
            )
        }
        _ => {
            if contains(&value::quote(ty, depth, budget)?, id, budget)? {
                Err(Error::InvalidPositivity)
            } else {
                Ok(())
            }
        }
    }
}
fn contains(term: &Tm, id: u64, budget: &mut Budget) -> Result<bool, Error> {
    budget.tick()?;
    if matches!(term.as_ref(), Term::Data { op, .. } if op.id() == id) {
        return Ok(true);
    }
    for child in children(term) {
        if contains(child, id, budget)? {
            return Ok(true);
        }
    }
    Ok(false)
}
fn reject_recursive_operations(term: &Tm, id: u64, budget: &mut Budget) -> Result<(), Error> {
    budget.tick()?;
    if matches!(term.as_ref(), Term::Data { op, .. } if op.id() == id && !matches!(op, DataOp::Type(_)))
    {
        return Err(Error::InvalidPositivity);
    }
    for child in children(term) {
        reject_recursive_operations(child, id, budget)?;
    }
    Ok(())
}

pub(super) fn children(term: &Tm) -> Vec<&Tm> {
    match term.as_ref() {
        Term::Data { arguments, .. } => arguments.iter().collect(),
        Term::Inductive { parameters, .. } => parameters.iter().collect(),
        Term::Constructor {
            parameters, fields, ..
        } => parameters.iter().chain(fields).collect(),
        Term::Elim {
            parameters,
            motive,
            branch,
            scrutinee,
            ..
        } => parameters
            .iter()
            .chain([motive, branch, scrutinee])
            .collect(),
        Term::Pi {
            domain, codomain, ..
        }
        | Term::Sigma { domain, codomain } => vec![domain, codomain],
        Term::Lam { domain, body, .. } => vec![domain, body],
        Term::App { function, argument } => vec![function, argument],
        Term::Let { ty, value, body } => vec![ty, value, body],
        Term::Pair { ty, fst, snd } => vec![ty, fst, snd],
        Term::Fst(t) | Term::Snd(t) => vec![t],
        Term::Eq { ty, left, right } => vec![ty, left, right],
        Term::Refl { ty, value } => vec![ty, value],
        Term::J {
            ty,
            left,
            motive,
            base,
            right,
            proof,
            ..
        } => vec![ty, left, motive, base, right, proof],

        Term::Global(_) | Term::Var(_) | Term::Universe(_) => vec![],
    }
}

impl Kernel {
    pub fn data_type_function(&self, id: u64) -> Result<Tm, Error> {
        let decl = self.data_declaration(id)?;
        let domains = decl
            .parameters
            .iter()
            .map(|ty| (Relevance::Erased, ty.clone()))
            .chain(
                decl.indices
                    .iter()
                    .map(|ty| (Relevance::Runtime, ty.clone())),
            )
            .collect::<Vec<_>>();
        self.data_function(DataOp::Type(id), domains)
    }
    pub fn data_constructor_function(&self, id: u64, constructor: usize) -> Result<Tm, Error> {
        let decl = self.data_declaration(id)?;
        let ctor = decl
            .constructors
            .get(constructor)
            .ok_or(Error::ArityMismatch)?;
        let domains = decl
            .parameters
            .iter()
            .map(|ty| (Relevance::Erased, ty.clone()))
            .chain(
                ctor.fields
                    .iter()
                    .map(|ty| (Relevance::Runtime, ty.clone())),
            )
            .collect();
        self.data_function(DataOp::Constructor(id, constructor), domains)
    }
    pub fn data_eliminator_function(&self, id: u64, level: u32) -> Result<Tm, Error> {
        let decl = self.data_declaration(id)?;
        let mut budget = Budget(self.max_steps, self.definitions.clone(), self.data.clone());
        let mut env = vec![];
        let mut domains = vec![];
        for ty in decl.parameters.iter().chain(&decl.indices) {
            domains.push((Relevance::Erased, ty.clone()));
            env.push(value::fresh(env.len()));
        }
        let params = env[..decl.parameters.len()].to_vec();
        let type_arguments = env.clone();
        let motive_ty = telescope(
            Arc::new(decl.indices.clone()),
            0,
            params.clone(),
            Arc::new(move |env, _| {
                Ok(Arc::new(Value::Pi(
                    Relevance::Runtime,
                    nominal(id, env.clone()),
                    Closure::Native(Arc::new(move |_, _| Ok(Arc::new(Value::Universe(level))))),
                )))
            }),
            &mut budget,
        )?;
        domains.push((
            Relevance::Runtime,
            value::quote(&motive_ty, env.len(), &mut budget)?,
        ));
        let motive = value::fresh(env.len());
        env.push(motive.clone());
        for c in 0..decl.constructors.len() {
            let ty = branch_type(id, c, &decl, params.clone(), motive.clone(), &mut budget)?;
            domains.push((
                Relevance::Runtime,
                value::quote(&ty, env.len(), &mut budget)?,
            ));
            env.push(value::fresh(env.len()));
        }
        domains.push((
            Relevance::Runtime,
            value::quote(&nominal(id, type_arguments), env.len(), &mut budget)?,
        ));
        self.data_function(DataOp::Eliminate(id, level), domains)
    }
    fn data_function(&self, op: DataOp, domains: Vec<(Relevance, Tm)>) -> Result<Tm, Error> {
        let mut body = Term::Data {
            op,
            arguments: (0..domains.len())
                .rev()
                .map(|i| Term::Var(i).arc())
                .collect(),
        }
        .arc();
        for (relevance, domain) in domains.into_iter().rev() {
            body = Term::Lam {
                relevance,
                domain,
                body,
            }
            .arc();
        }
        self.infer(&body)?;
        Ok(body)
    }
}

// Rigid constructor clashes are evidence of impossibility. Neutral terms,
// arbitrary equations and occurs checks never justify removing a branch.
fn disjoint(a: &Val, b: &Val, budget: &mut Budget) -> Result<bool, Error> {
    budget.tick()?;
    match (a.as_ref(), b.as_ref()) {
        (
            Value::Data {
                op: DataOp::Constructor(id, c),
                arguments: left,
            },
            Value::Data {
                op: DataOp::Constructor(other, d),
                arguments: right,
            },
        ) if id == other => {
            if c != d {
                return Ok(true);
            }
            let p = declaration(*id, budget)?.parameters.len();
            for (a, b) in left[p..].iter().zip(&right[p..]) {
                if disjoint(a, b, budget)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Ok(false),
    }
}
