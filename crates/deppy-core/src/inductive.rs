use crate::{Error, Kernel, Relevance, Term, Tm};
pub type InductiveId = u64;
/// A nonrecursive single-constructor inductive, with no indices.
/// Each telescope entry is scoped over parameters and earlier entries only.
#[derive(Clone, Debug)]
pub struct InductiveDecl {
    pub parameters: Vec<Tm>,
    pub fields: Vec<Tm>,
    pub level: u32,
}
fn var(i: usize) -> Tm {
    Term::Var(i).arc()
}
fn apply(f: Tm, args: impl IntoIterator<Item = Tm>) -> Tm {
    args.into_iter().fold(f, |function, argument| {
        Term::App { function, argument }.arc()
    })
}
fn bind(types: &[Tm], body: Tm, relevance: Relevance) -> Tm {
    types.iter().rev().fold(body, |body, domain| {
        Term::Lam {
            relevance,
            domain: domain.clone(),
            body,
        }
        .arc()
    })
}
fn params(count: usize, offset: usize) -> Vec<Tm> {
    (0..count).rev().map(|i| var(i + offset)).collect()
}
impl Kernel {
    pub fn inductive_function(&self, id: InductiveId) -> Result<Tm, Error> {
        let d = self.declaration(id)?;
        Ok(bind(
            &d.parameters,
            Term::Inductive {
                id,
                parameters: params(d.parameters.len(), 0),
            }
            .arc(),
            Relevance::Erased,
        ))
    }
    pub fn constructor_function(&self, id: InductiveId) -> Result<Tm, Error> {
        let d = self.declaration(id)?;
        let ctor = Term::Constructor {
            id,
            parameters: params(d.parameters.len(), d.fields.len()),
            fields: params(d.fields.len(), 0),
        }
        .arc();
        Ok(bind(
            &d.parameters,
            bind(&d.fields, ctor, Relevance::Runtime),
            Relevance::Erased,
        ))
    }
    /// Generate dependent projections via elimination; there is no record primitive or eta rule.
    pub fn projection_functions(&self, id: InductiveId) -> Result<Vec<Tm>, Error> {
        let d = self.declaration(id)?;
        let count = d.parameters.len();
        let mut projections: Vec<Tm> = vec![];
        for (index, field_ty) in d.fields.iter().enumerate() {
            let nominal = Term::Inductive {
                id,
                parameters: params(count, 0),
            }
            .arc();
            // Close the field type over its telescope, then instantiate earlier fields
            // with their generated projections. This avoids shifting caller syntax.
            let family = bind(
                &d.parameters,
                bind(&d.fields[..index], field_ty.clone(), Relevance::Runtime),
                Relevance::Erased,
            );
            let arguments = params(count, 1).into_iter().chain(
                projections
                    .iter()
                    .map(|p| apply(apply(p.clone(), params(count, 1)), [var(0)])),
            );
            let result_ty = apply(family, arguments);
            let motive = bind(
                &d.parameters,
                Term::Lam {
                    relevance: Relevance::Runtime,
                    domain: nominal.clone(),
                    body: result_ty,
                }
                .arc(),
                Relevance::Erased,
            );
            // The inferred motive signature ends in Type[level], possibly smaller than d.level.
            let mut motive_ty = self.infer(&motive)?;
            while let Term::Pi { codomain, .. } = motive_ty.as_ref() {
                motive_ty = codomain.clone();
            }
            let Term::Universe(level) = motive_ty.as_ref() else {
                return Err(Error::ExpectedUniverse);
            };
            let branch = bind(
                &d.parameters,
                bind(
                    &d.fields,
                    var(d.fields.len() - 1 - index),
                    Relevance::Runtime,
                ),
                Relevance::Erased,
            );
            let elim = Term::Elim {
                id,
                parameters: params(count, 1),
                level: *level,
                motive: apply(motive, params(count, 1)),
                branch: apply(branch, params(count, 1)),
                scrutinee: var(0),
            }
            .arc();
            let projection = bind(
                &d.parameters,
                Term::Lam {
                    relevance: Relevance::Runtime,
                    domain: nominal,
                    body: elim,
                }
                .arc(),
                Relevance::Erased,
            );
            self.infer(&projection)?;
            projections.push(projection);
        }
        Ok(projections)
    }
}
