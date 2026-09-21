use super::*;
impl Lowerer {
    pub(super) fn rewrite(
        &mut self,
        e: &E,
        env: &Env,
        recursion: Option<&Recursion>,
    ) -> Result<E, Error> {
        self.tick()?;
        Ok(match e {
            E::Rewrite {
                proof,
                body,
                forward,
            } => E::Rewrite {
                proof: Box::new(self.rewrite(proof, env, recursion)?),
                body: Box::new(self.rewrite(body, env, recursion)?),
                forward: *forward,
            },
            E::Cases {
                level,
                value,
                branches,
                generalize,
            } => {
                let value = Box::new(self.rewrite(value, env, recursion)?);
                let mut case_env = env.clone();
                let mut dependencies = vec![];
                for (name, expr) in generalize {
                    let expr = self.rewrite(expr, env, recursion)?;
                    let name = self.bind(&mut case_env, name)?;
                    dependencies.push((name, expr));
                }
                let mut rewritten = vec![];
                for branch in branches {
                    let mut inner = case_env.clone();
                    let fields = branch
                        .fields
                        .iter()
                        .map(|n| self.bind(&mut inner, n))
                        .collect::<Result<_, _>>()?;
                    rewritten.push(crate::CaseBranch {
                        constructor: branch.constructor.clone(),
                        fields,
                        body: self.rewrite(&branch.body, &inner, recursion)?,
                        location: branch.location.clone(),
                    });
                }
                E::Cases {
                    level: *level,
                    value,
                    branches: rewritten,
                    generalize: dependencies,
                }
            }
            E::Absurd { ty, value } => E::Absurd {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                value: Box::new(self.rewrite(value, env, recursion)?),
            },
            E::Induct {
                level,
                value,
                motive,
                branches,
            } => E::Induct {
                level: *level,
                value: Box::new(self.rewrite(value, env, recursion)?),
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                branches: branches
                    .iter()
                    .map(|b| self.rewrite(b, env, recursion))
                    .collect::<Result<_, _>>()?,
            },
            E::UserHole(name) => E::UserHole(name.clone()),
            E::Located {
                location,
                expression,
            } => self
                .rewrite(expression, env, recursion)
                .map_err(|e| e.at(location))?
                .located(location.clone()),
            E::Let {
                name,
                ty,
                value,
                body,
            } => {
                let ty = ty
                    .as_deref()
                    .map(|ty| self.rewrite(ty, env, recursion))
                    .transpose()?;
                let value = self.rewrite(value, env, recursion)?;
                let mut inner = env.clone();
                let name = self.bind(&mut inner, name)?;
                E::let_in(name, ty, value, self.rewrite(body, &inner, recursion)?)
            }
            E::Name(name) => {
                if !self.generated {
                    Self::name(name)?;
                }
                env.get(name)
                    .cloned()
                    .ok_or_else(|| Error::UnknownName(name.clone()))?
            }
            E::Core(term) => E::Core(term.clone()),
            E::Universe(level) => E::Universe(*level),
            E::Nat => E::Nat,
            E::Zero => E::Zero,
            E::Hole => E::Hole,
            E::Recur(arguments) => {
                if !self.alternatives.is_empty() {
                    let alternatives = std::mem::take(&mut self.alternatives);
                    let mut result = Err(Error::InvalidRecursion(
                        "no matching structural child".into(),
                    ));
                    for candidate in &alternatives {
                        result = self.rewrite(e, env, Some(candidate));
                        if !matches!(&result, Err(error) if matches!(error.cause(), Error::InvalidRecursion(_)))
                        {
                            break;
                        }
                    }
                    self.alternatives = alternatives;
                    return result;
                }
                let rec = recursion.ok_or_else(|| {
                    Error::InvalidRecursion("no smaller recursive field in this branch".into())
                })?;
                if arguments.len() != rec.arguments.len() {
                    return Err(Error::InvalidRecursion(
                        "self-call requires every declared argument".into(),
                    ));
                }
                let mut call = rec.ih.clone();
                let mut validation = rec.signature.clone();
                let mut suffix = rec.suffix.iter();
                for (position, (arg, expected)) in arguments.iter().zip(&rec.arguments).enumerate()
                {
                    let arg = self.rewrite(arg, env, recursion)?;
                    if let Some(checker) = validation.take() {
                        // The checker has the original parameter telescope. Its
                        // application validates refined/compound index arguments.
                        let argument = if rec.indices.contains(&position)
                            && rec.plicities[position] == Plicity::Implicit
                        {
                            E::Hole
                        } else {
                            arg.clone()
                        };
                        validation = Some(apply(checker, argument, rec.plicities[position]));
                    }
                    if rec.signature.is_some() && rec.indices.contains(&position) {
                        continue;
                    }
                    if let Some(expected) = expected {
                        if !matches!(arg.unlocated(),E::Name(actual) if actual==expected) {
                            return Err(Error::InvalidRecursion("self-call must use the direct recursive field, its index, and unchanged prefix parameters".into()));
                        }
                    } else {
                        call = apply(call, arg, *suffix.next().unwrap());
                    }
                }
                if let Some(validation) = validation {
                    E::let_in(self.fresh(), None, validation, call)
                } else {
                    call
                }
            }
            E::Pi {
                name,
                plicity,
                domain,
                codomain,
            } => {
                let domain = self.rewrite(domain, env, recursion)?;
                let mut env = env.clone();
                let name = self.bind(&mut env, name)?;
                E::pi(
                    name,
                    *plicity,
                    domain,
                    self.rewrite(codomain, &env, recursion)?,
                )
            }
            E::Sigma {
                name,
                domain,
                codomain,
            } => {
                let domain = self.rewrite(domain, env, recursion)?;
                let mut env = env.clone();
                let name = self.bind(&mut env, name)?;
                E::sigma(name, domain, self.rewrite(codomain, &env, recursion)?)
            }
            E::Lam {
                name,
                plicity,
                domain,
                body,
            } => {
                let domain = domain
                    .as_ref()
                    .map(|d| self.rewrite(d, env, recursion))
                    .transpose()?;
                let mut env = env.clone();
                let name = self.bind(&mut env, name)?;
                E::lam(name, *plicity, domain, self.rewrite(body, &env, recursion)?)
            }
            E::RecordElim {
                level,
                motive,
                branch,
                value,
            } => E::RecordElim {
                level: *level,
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                branch: Box::new(self.rewrite(branch, env, recursion)?),
                value: Box::new(self.rewrite(value, env, recursion)?),
            },
            E::Field { value, name } => self.rewrite(value, env, recursion)?.field(name),
            E::Fst(x) => E::Fst(Box::new(self.rewrite(x, env, recursion)?)),
            E::Snd(x) => E::Snd(Box::new(self.rewrite(x, env, recursion)?)),
            E::Refl(x) => E::Refl(Box::new(self.rewrite(x, env, recursion)?)),
            E::Succ(x) => E::Succ(Box::new(self.rewrite(x, env, recursion)?)),
            E::App {
                function,
                argument,
                plicity,
            } => E::App {
                function: Box::new(self.rewrite(function, env, recursion)?),
                argument: Box::new(self.rewrite(argument, env, recursion)?),
                plicity: *plicity,
            },
            E::Ann { term, ty } => E::Ann {
                term: Box::new(self.rewrite(term, env, recursion)?),
                ty: Box::new(self.rewrite(ty, env, recursion)?),
            },
            E::Pair { fst, snd } => E::Pair {
                fst: Box::new(self.rewrite(fst, env, recursion)?),
                snd: Box::new(self.rewrite(snd, env, recursion)?),
            },
            E::Eq { ty, left, right } => E::Eq {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                left: Box::new(self.rewrite(left, env, recursion)?),
                right: Box::new(self.rewrite(right, env, recursion)?),
            },
            E::J {
                level,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            } => E::J {
                level: *level,
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                left: Box::new(self.rewrite(left, env, recursion)?),
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                base: Box::new(self.rewrite(base, env, recursion)?),
                right: Box::new(self.rewrite(right, env, recursion)?),
                proof: Box::new(self.rewrite(proof, env, recursion)?),
            },
            E::Vec { ty, len } => E::Vec {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                len: Box::new(self.rewrite(len, env, recursion)?),
            },
            E::VNil { ty } => E::VNil {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
            },
            E::VCons {
                ty,
                len,
                head,
                tail,
            } => E::VCons {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                len: Box::new(self.rewrite(len, env, recursion)?),
                head: Box::new(self.rewrite(head, env, recursion)?),
                tail: Box::new(self.rewrite(tail, env, recursion)?),
            },
            E::Fin { bound } => E::Fin {
                bound: Box::new(self.rewrite(bound, env, recursion)?),
            },
            E::FZ { bound } => E::FZ {
                bound: Box::new(self.rewrite(bound, env, recursion)?),
            },
            E::FS { bound, pred } => E::FS {
                bound: Box::new(self.rewrite(bound, env, recursion)?),
                pred: Box::new(self.rewrite(pred, env, recursion)?),
            },
            E::VecElim {
                level,
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
            } => E::VecElim {
                level: *level,
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                nil: Box::new(self.rewrite(nil, env, recursion)?),
                cons: Box::new(self.rewrite(cons, env, recursion)?),
                len: Box::new(self.rewrite(len, env, recursion)?),
                scrutinee: Box::new(self.rewrite(scrutinee, env, recursion)?),
            },
            E::FinElim {
                level,
                motive,
                zero,
                step,
                bound,
                scrutinee,
            } => E::FinElim {
                level: *level,
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                zero: Box::new(self.rewrite(zero, env, recursion)?),
                step: Box::new(self.rewrite(step, env, recursion)?),
                bound: Box::new(self.rewrite(bound, env, recursion)?),
                scrutinee: Box::new(self.rewrite(scrutinee, env, recursion)?),
            },
            E::Fin0Elim { ty, absurd } => E::Fin0Elim {
                ty: Box::new(self.rewrite(ty, env, recursion)?),
                absurd: Box::new(self.rewrite(absurd, env, recursion)?),
            },
            E::NatElim {
                level,
                motive,
                zero,
                step,
                scrutinee,
            } => E::NatElim {
                level: *level,
                motive: Box::new(self.rewrite(motive, env, recursion)?),
                zero: Box::new(self.rewrite(zero, env, recursion)?),
                step: Box::new(self.rewrite(step, env, recursion)?),
                scrutinee: Box::new(self.rewrite(scrutinee, env, recursion)?),
            },
        })
    }
}
