use super::*;
use deppy_core::DataOp;

impl State {
    fn lifted_expression(&mut self, term: &T, locals: &Context) -> Result<Expr, Error> {
        let mut scope = vec![];
        let saved = std::mem::take(&mut self.core_domains);
        let result = (|| {
            for local in locals {
                let ty = self.zonk(&local.ty)?;
                let ty = self.core(&ty, &mut scope)?;
                self.core_domains.push(ty);
                scope.push(local.id);
            }
            let term = self.zonk(term)?;
            let mut term = self.core(&term, &mut scope)?;
            for (ty, local) in self.core_domains.iter().zip(locals).rev() {
                term = Core::Lam {
                    relevance: local.plicity.relevance(),
                    domain: ty.clone(),
                    body: term,
                }
                .arc();
            }
            Ok(locals.iter().fold(Expr::Core(term), |f, local| {
                let arg = Expr::name(format!("\0lift:{}", local.id));
                if local.plicity == Plicity::Implicit {
                    f.implicit(arg)
                } else {
                    f.app(arg)
                }
            }))
        })();
        self.core_domains = saved;
        result
    }

    fn fixed_cases(
        &mut self,
        ctx: &Context,
        level: u32,
        subject: Id,
        branches: &[crate::CaseBranch],
        generalize: &[(String, Expr)],
        expected: &T,
    ) -> Result<T, Error> {
        use crate::lower::{Arm, Body, Function, Parameter, Pattern};
        let mut locals = ctx
            .iter()
            .filter(|local| local.value.is_none())
            .cloned()
            .collect::<Context>();
        let referenced = |name: &str| {
            branches.iter().any(|branch| {
                branch
                    .body
                    .any(&|e| matches!(e, Expr::Name(n) if n == name))
            })
        };
        let visible = ctx
            .iter()
            .enumerate()
            .filter(|(i, local)| {
                !ctx[i + 1..].iter().any(|later| later.name == local.name)
                    && referenced(&local.name)
            })
            .map(|(_, local)| local)
            .collect::<Vec<_>>();
        let mut pending = vec![self.zonk(expected)?];
        let mut required = HashSet::from([subject]);
        for local in &visible {
            pending.push(self.zonk(local.value.as_ref().unwrap_or(&Term::Local(local.id).arc()))?);
        }
        let mut dependencies = vec![];
        for (_, expression) in generalize {
            let (value, ty) = self.synth(ctx, expression)?;
            pending.push(self.zonk(&value)?);
            pending.push(self.zonk(&ty)?);
            dependencies.push((value, ty));
        }
        pending.push(
            self.zonk(
                &locals
                    .iter()
                    .find(|l| l.id == subject)
                    .ok_or(Error::ScopeEscape)?
                    .ty,
            )?,
        );
        let all = locals.iter().map(|local| local.id).collect::<HashSet<_>>();
        while let Some(term) = pending.pop() {
            for local in &locals {
                if required.contains(&local.id) {
                    continue;
                }
                let mut allowed = all.clone();
                allowed.remove(&local.id);
                match self.validate_solution(usize::MAX, &term, &mut allowed) {
                    Err(Error::ScopeEscape) => {
                        required.insert(local.id);
                        pending.push(self.zonk(&local.ty)?);
                    }
                    result => result?,
                }
            }
        }
        locals.retain(|local| required.contains(&local.id));
        let subject_local = locals
            .iter()
            .find(|local| local.id == subject)
            .ok_or(Error::ScopeEscape)?
            .clone();
        let all = locals.iter().map(|local| local.id).collect::<HashSet<_>>();
        // Universe-valued locals stay outside the motive, avoiding an
        // unnecessary universe increase when matching a small indexed value.
        let mut needed = HashSet::new();
        for local in &locals {
            if matches!(self.whnf(&local.ty)?.as_ref(), Term::Universe(_)) {
                needed.insert(local.id);
            }
        }
        let mut pending = vec![self.zonk(&subject_local.ty)?];
        while let Some(ty) = pending.pop() {
            for local in &locals {
                if local.id == subject || needed.contains(&local.id) {
                    continue;
                }
                let mut allowed = all.clone();
                allowed.remove(&local.id);
                match self.validate_solution(usize::MAX, &ty, &mut allowed) {
                    Err(Error::ScopeEscape) => {
                        needed.insert(local.id);
                        pending.push(self.zonk(&local.ty)?);
                    }
                    result => result?,
                }
            }
        }
        let mut ordered = locals
            .iter()
            .filter(|local| needed.contains(&local.id))
            .cloned()
            .collect::<Context>();
        let d = ordered.len();
        ordered.push(subject_local);
        ordered.extend(
            locals
                .iter()
                .filter(|local| local.id != subject && !needed.contains(&local.id))
                .cloned(),
        );
        let mut parameters = vec![];
        for (i, local) in ordered.iter().enumerate() {
            parameters.push(Parameter {
                name: format!("\0lift:{}", local.id),
                plicity: local.plicity,
                ty: self.lifted_expression(&local.ty, &ordered[..i].to_vec())?,
            });
        }
        let mut globals = self
            .globals
            .iter()
            .map(|(name, id)| (name.clone(), Expr::Core(Core::Global(*id).arc())))
            .collect::<HashMap<_, _>>();
        for local in visible {
            let value = match &local.value {
                Some(value) => self.lifted_expression(value, &ordered)?,
                None => Expr::name(format!("\0lift:{}", local.id)),
            };
            globals.insert(local.name.clone(), value);
        }
        for ((name, _), (_, ty)) in generalize.iter().zip(&dependencies) {
            parameters.push(Parameter {
                name: name.clone(),
                plicity: Plicity::Explicit,
                ty: self.lifted_expression(ty, &ordered)?,
            });
        }
        let result = self.lifted_expression(expected, &ordered)?;
        let mut scope = vec![];
        let saved = std::mem::take(&mut self.core_domains);
        let prefix_result: Result<_, Error> = (|| {
            for local in &ordered[..d] {
                let ty = self.zonk(&local.ty)?;
                let ty = self.core(&ty, &mut scope)?;
                self.core_domains.push(ty);
                scope.push(local.id);
            }
            let receiver = self.zonk(&ordered[d].ty)?;
            let receiver = self.core(&receiver, &mut scope)?;
            Ok((receiver, self.core_domains.clone()))
        })();
        self.core_domains = saved;
        let (receiver, prefix) = prefix_result?;
        let Core::Data {
            op: DataOp::Type(family),
            arguments,
        } = receiver.as_ref()
        else {
            return Err(Error::ExpectedInductive);
        };
        let mut arms = vec![];
        for (i, branch) in branches.iter().enumerate() {
            let name = match &branch.constructor {
                crate::CaseConstructor::Name(name) => name.clone(),
                crate::CaseConstructor::Core(id, c) => {
                    let name = format!("$lifted_constructor{i}");
                    globals.insert(
                        name.clone(),
                        Expr::Core(self.kernel.data_constructor_function(*id, *c)?),
                    );
                    name
                }
            };
            let pattern = Pattern::Constructor {
                name,
                fields: branch.fields.clone(),
            };
            arms.push(Arm {
                pattern: branch
                    .location
                    .as_ref()
                    .map_or(pattern.clone(), |location| {
                        pattern.located(location.clone())
                    }),
                body: Body::Return(branch.body.clone()),
            });
        }
        let subject_name = parameters[d].name.clone();
        let function = Function {
            parameters,
            result,
            decreases: subject_name.clone(),
            motive_level: level,
            body: Body::Match {
                scrutinee: subject_name,
                arms,
            },
        };
        let expression = crate::lower::lifted_cases(
            self.kernel.clone(),
            &mut self.remaining,
            globals,
            function,
            *family,
            arguments.clone(),
            prefix,
        )?;
        let (mut function, mut ty) = self.synth(ctx, &expression)?;
        for local in &ordered {
            self.case_apply(&mut function, &mut ty, Term::Local(local.id).arc())?;
        }
        for (value, _) in dependencies {
            self.case_apply(&mut function, &mut ty, value)?;
        }
        self.unify(&ty, expected)?;
        Ok(function)
    }
    fn case_apply(&mut self, function: &mut T, ty: &mut T, argument: T) -> Result<(), Error> {
        let head = self.whnf(ty)?;
        let Term::Pi { id, body, .. } = head.as_ref() else {
            return Err(Error::ExpectedFunction);
        };
        *ty = self.replace(body, *id, argument.clone())?;
        *function = Term::App(function.clone(), argument).arc();
        Ok(())
    }

    pub(super) fn cases(
        &mut self,
        ctx: &Context,
        level: u32,
        value: &Expr,
        branches: &[crate::CaseBranch],
        generalize: &[(String, Expr)],
        expected: &T,
    ) -> Result<T, Error> {
        let mut dependency_names = generalize
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let mut dependency_modes = vec![Plicity::Explicit; generalize.len()];
        let mut dependencies = generalize
            .iter()
            .map(|(_, e)| self.synth(ctx, e))
            .collect::<Result<Vec<_>, _>>()?;
        let (value, receiver) = self.synth(ctx, value)?;
        let receiver = self.whnf(&receiver)?;
        let receiver = match receiver.as_ref() {
            Term::Nat => Term::Data {
                op: DataOp::Type(deppy_core::standard::NAT),
                arguments: vec![],
            }
            .arc(),
            Term::Fin { bound } => Term::Data {
                op: DataOp::Type(deppy_core::standard::FIN),
                arguments: vec![bound.clone()],
            }
            .arc(),
            _ => receiver,
        };
        if let Term::Local(subject) = value.as_ref() {
            if let Some(position) = ctx.iter().position(|local| local.id == *subject) {
                let mut automatic = vec![];
                let mut names = vec![];
                let mut modes = vec![];
                for local in &ctx[position + 1..] {
                    if local.value.is_some() {
                        continue;
                    }
                    if dependencies.iter().any(
                        |(term, _)| matches!(term.as_ref(), Term::Local(id) if *id == local.id),
                    ) {
                        continue;
                    }
                    names.push(local.name.clone());
                    modes.push(local.plicity);
                    automatic.push((Term::Local(local.id).arc(), local.ty.clone()));
                }
                names.append(&mut dependency_names);
                modes.append(&mut dependency_modes);
                automatic.append(&mut dependencies);
                dependency_names = names;
                dependency_modes = modes;
                dependencies = automatic;
            }
        }
        let Term::Data {
            op: DataOp::Type(family),
            arguments,
        } = receiver.as_ref()
        else {
            return Err(Error::ExpectedInductive);
        };
        let declaration = self.kernel.data_declaration(*family)?;
        let p = declaration.parameters.len();
        if arguments[p..]
            .iter()
            .any(|index| !matches!(index.as_ref(), Term::Local(_)))
        {
            if let Term::Local(subject) = value.as_ref() {
                return self.fixed_cases(ctx, level, *subject, branches, generalize, expected);
            }
        }
        let mut ordered = vec![None; declaration.constructors.len()];
        for branch in branches {
            let result = (|| {
                let (id, c) = match &branch.constructor {
                    crate::CaseConstructor::Core(id, c) => (*id, *c),
                    crate::CaseConstructor::Name(name) => {
                        let id = self
                            .globals
                            .get(name)
                            .ok_or_else(|| Error::UnknownName(name.clone()))?;
                        let mut constructor = self.kernel.normalize(&Core::Global(*id).arc())?;
                        while let Core::Lam { body, .. } = constructor.as_ref() {
                            constructor = body.clone();
                        }
                        let Core::Data {
                            op: DataOp::Constructor(id, c),
                            ..
                        } = constructor.as_ref()
                        else {
                            return Err(Error::InvalidPattern("expected a constructor".into()));
                        };
                        (*id, *c)
                    }
                };
                if id != *family
                    || declaration
                        .constructors
                        .get(c)
                        .is_none_or(|ctor| ctor.fields.len() != branch.fields.len())
                {
                    return Err(Error::InvalidPattern(
                        "wrong family or constructor arity".into(),
                    ));
                }
                if ordered[c].replace(branch).is_some() {
                    return Err(Error::InvalidPattern("duplicate constructor branch".into()));
                }
                Ok(())
            })();
            result.map_err(|e| match &branch.location {
                Some(l) => e.at(l),
                None => e,
            })?;
        }
        if ordered.iter().any(Option::is_none) {
            return Err(Error::InvalidPattern(
                "match must cover every constructor".into(),
            ));
        }
        let function = Expr::Core(self.kernel.data_eliminator_function(*family, level)?);
        let (mut function, mut ty) = self.synth(ctx, &function)?;
        for argument in arguments {
            self.case_apply(&mut function, &mut ty, argument.clone())?;
        }
        let head = self.whnf(&ty)?;
        let Term::Pi { domain, .. } = head.as_ref() else {
            return Err(Error::ExpectedFunction);
        };
        let mut motive_ty = domain.clone();
        let mut result = expected.clone();
        let mut dependency_types = dependencies
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>();
        let mut motive_binders = vec![];
        for original in arguments[p..].iter().chain([&value]) {
            let head = self.whnf(&motive_ty)?;
            let Term::Pi {
                id, domain, body, ..
            } = head.as_ref()
            else {
                return Err(Error::ExpectedFunction);
            };
            let fresh = self.fresh();
            let variable = Term::Local(fresh).arc();
            if let Term::Local(original) = original.as_ref() {
                result = self.replace(&result, *original, variable.clone())?;
                for ty in &mut dependency_types {
                    *ty = self.replace(ty, *original, variable.clone())?;
                }
            }
            motive_binders.push((fresh, domain.clone()));
            motive_ty = self.replace(body, *id, variable)?;
        }
        let mut dependency_binders = vec![];
        for i in 0..dependencies.len() {
            let fresh = self.fresh();
            if let Term::Local(original) = dependencies[i].0.as_ref() {
                result = self.replace(&result, *original, Term::Local(fresh).arc())?;
                for ty in &mut dependency_types[i + 1..] {
                    *ty = self.replace(ty, *original, Term::Local(fresh).arc())?;
                }
            }
            dependency_binders.push((fresh, dependency_modes[i], dependency_types[i].clone()));
        }
        for (id, plicity, domain) in dependency_binders.into_iter().rev() {
            result = Term::Pi {
                id,
                plicity,
                domain,
                body: result,
            }
            .arc();
        }
        for (id, domain) in motive_binders.into_iter().rev() {
            result = Term::Lam {
                id,
                plicity: Plicity::Explicit,
                domain,
                body: result,
            }
            .arc();
        }
        self.case_apply(&mut function, &mut ty, result)?;
        for (c, branch) in ordered.into_iter().enumerate() {
            let branch = branch.unwrap();
            let head = self.whnf(&ty)?;
            let Term::Pi { domain, .. } = head.as_ref() else {
                return Err(Error::ExpectedFunction);
            };
            let mut branch_ty = domain.clone();
            let mut inner = ctx.clone();
            let mut binders = vec![];
            let mut fields = vec![];
            let mut names = HashSet::new();
            // Only the constructor fields and generated IHs belong to the branch
            // telescope. The branch result may itself be a function.
            let ctor = &declaration.constructors[c];
            let recursive = ctor
                .fields
                .iter()
                .filter(|field| {
                    let mut field = field.as_ref();
                    while let Core::Pi { codomain, .. } = field {
                        field = codomain.as_ref();
                    }
                    matches!(field, Core::Data { op: DataOp::Type(id), .. } if id == family)
                })
                .count();
            for i in 0..branch.fields.len() + recursive {
                let head = self.whnf(&branch_ty)?;
                let Term::Pi {
                    id,
                    domain,
                    body,
                    plicity,
                } = head.as_ref()
                else {
                    return Err(Error::ExpectedFunction);
                };
                let name = branch
                    .fields
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("$case_ih{i}"));
                if !names.insert(name.clone()) {
                    return Err(Error::InvalidPattern("duplicate pattern binding".into()));
                }
                let (next, fresh) = self.bind(&inner, &name, domain.clone());
                inner = next;
                inner.last_mut().unwrap().plicity = *plicity;
                let variable = Term::Local(fresh).arc();
                if i < branch.fields.len() {
                    fields.push(variable.clone());
                }
                binders.push((fresh, *plicity, domain.clone()));
                branch_ty = self.replace(body, *id, variable)?;
            }
            if let Term::Local(subject) = value.as_ref() {
                let expression = Expr::Core(self.kernel.data_constructor_function(*family, c)?);
                let (mut constructor, mut ty) = self.synth(ctx, &expression)?;
                for arg in arguments[..p].iter().cloned().chain(fields) {
                    self.case_apply(&mut constructor, &mut ty, arg)?;
                }
                let constructor = self.whnf(&constructor)?;
                let refined = self.whnf(&ty)?;
                if let Term::Data {
                    arguments: refined, ..
                } = refined.as_ref()
                {
                    for (original, refined) in arguments[p..].iter().zip(&refined[p..]) {
                        if let Term::Local(index) = original.as_ref() {
                            if let Some(local) = ctx.iter().find(|local| local.id == *index) {
                                let (next, alias) =
                                    self.bind(&inner, &local.name, local.ty.clone());
                                inner = next;
                                inner
                                    .iter_mut()
                                    .find(|local| local.id == alias)
                                    .unwrap()
                                    .value = Some(refined.clone());
                            }
                        }
                    }
                }
                if let Some(local) = ctx.iter().find(|local| local.id == *subject) {
                    // Keep the original telescope intact: earlier dependent
                    // locals still mention this variable. Refine its source
                    // name with a let alias instead of removing that binder.
                    let (next, alias) = self.bind(&inner, &local.name, ty);
                    inner = next;
                    inner
                        .iter_mut()
                        .find(|local| local.id == alias)
                        .unwrap()
                        .value = Some(constructor);
                }
            }
            for name in &dependency_names {
                let head = self.whnf(&branch_ty)?;
                let Term::Pi {
                    id,
                    domain,
                    body,
                    plicity,
                } = head.as_ref()
                else {
                    return Err(Error::ExpectedFunction);
                };
                let (next, fresh) = self.bind(&inner, name, domain.clone());
                inner = next;
                inner.last_mut().unwrap().plicity = *plicity;
                binders.push((fresh, *plicity, domain.clone()));
                branch_ty = self.replace(body, *id, Term::Local(fresh).arc())?;
            }
            let mut body =
                self.check(&inner, &branch.body, &branch_ty).map_err(|e| {
                    match &branch.location {
                        Some(l) => e.at(l),
                        None => e,
                    }
                })?;
            for (id, plicity, domain) in binders.into_iter().rev() {
                body = Term::Lam {
                    id,
                    plicity,
                    domain,
                    body,
                }
                .arc();
            }
            self.case_apply(&mut function, &mut ty, body)?;
        }
        self.case_apply(&mut function, &mut ty, value)?;
        for (value, _) in dependencies {
            self.case_apply(&mut function, &mut ty, value)?;
        }
        self.unify(&ty, expected)?;
        Ok(function)
    }
}
