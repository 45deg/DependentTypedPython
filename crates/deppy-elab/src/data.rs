use crate::{Elaborator, Error, Expr, Plicity};
use deppy_core::{ConstructorDecl, DataDecl, DataOp, Term, Tm};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct NamedConstructor {
    pub name: String,
    pub fields: Vec<(String, Expr)>,
    pub result: Expr,
}
#[derive(Clone, Debug)]
pub struct NamedDataDecl {
    pub name: String,
    pub parameters: Vec<(String, Expr)>,
    pub indices: Vec<(String, Expr)>,
    pub constructors: Vec<NamedConstructor>,
    pub level: u32,
}
fn telescope(entries: &[(String, Expr)], result: Expr) -> Expr {
    entries.iter().rev().fold(result, |body, (name, ty)| {
        Expr::pi(name, Plicity::Explicit, ty.clone(), body)
    })
}
fn domains(mut term: Tm, count: usize) -> Result<(Vec<Tm>, Tm), Error> {
    let mut result = vec![];
    for _ in 0..count {
        let Term::Pi {
            domain, codomain, ..
        } = term.as_ref()
        else {
            return Err(Error::ExpectedFunction);
        };
        result.push(domain.clone());
        term = codomain.clone();
    }
    Ok((result, term))
}
impl Elaborator {
    /// Register the family and all constructors atomically after independent kernel validation.
    pub fn declare_data(
        &mut self,
        id: u64,
        decl: NamedDataDecl,
    ) -> Result<Vec<(String, u64)>, Error> {
        let mut names = HashSet::new();
        for name in std::iter::once(&decl.name).chain(decl.constructors.iter().map(|c| &c.name)) {
            if name.is_empty() || !names.insert(name) || self.globals.contains_key(name) {
                return Err(Error::InvalidDeclarationName(name.clone()));
            }
        }
        let mut binders = HashSet::new();
        for (name, _) in decl.parameters.iter().chain(&decl.indices) {
            if name.is_empty() || !binders.insert(name) {
                return Err(Error::InvalidDeclarationName(name.clone()));
            }
        }
        let entries = decl
            .parameters
            .iter()
            .chain(&decl.indices)
            .cloned()
            .collect::<Vec<_>>();
        let header = self.infer(&telescope(&entries, Expr::Universe(0)))?;
        let (parameters, tail) =
            domains(self.kernel.normalize(&header.term)?, decl.parameters.len())?;
        let (indices, _) = domains(tail, decl.indices.len())?;
        let mut core = DataDecl {
            parameters,
            indices,
            constructors: vec![],
            level: decl.level,
        };
        let mut provisional = self.clone();
        provisional.kernel.declare_data(id, core.clone())?;
        provisional.define(
            &decl.name,
            None,
            &Expr::Core(provisional.kernel.data_type_function(id)?),
        )?;
        for constructor in &decl.constructors {
            let mut names = decl
                .parameters
                .iter()
                .map(|(name, _)| name)
                .collect::<HashSet<_>>();
            for (name, _) in &constructor.fields {
                if name.is_empty() || !names.insert(name) {
                    return Err(Error::InvalidDeclarationName(name.clone()));
                }
            }
            let entries = decl
                .parameters
                .iter()
                .chain(&constructor.fields)
                .cloned()
                .collect::<Vec<_>>();
            let signature = provisional.infer(&telescope(&entries, constructor.result.clone()))?;
            let (_, tail) = domains(
                provisional.kernel.normalize(&signature.term)?,
                decl.parameters.len(),
            )?;
            let (fields, result) = domains(tail, constructor.fields.len())?;
            let Term::Data {
                op: DataOp::Type(result_id),
                arguments,
            } = result.as_ref()
            else {
                return Err(Error::ExpectedUniverse);
            };
            let p = decl.parameters.len();
            if *result_id != id
                || arguments.len() != p + decl.indices.len()
                || arguments[..p]
                    .iter()
                    .enumerate()
                    .any(|(i, arg)| arg.as_ref() != &Term::Var(p + fields.len() - i - 1))
            {
                return Err(deppy_core::Error::InvalidPositivity.into());
            }
            core.constructors.push(ConstructorDecl {
                fields,
                indices: arguments[p..].to_vec(),
            });
        }
        let mut checked = self.clone();
        checked.kernel.declare_data(id, core)?;
        let mut exports = vec![(
            decl.name.clone(),
            checked.define(
                &decl.name,
                None,
                &Expr::Core(checked.kernel.data_type_function(id)?),
            )?,
        )];
        for (c, constructor) in decl.constructors.iter().enumerate() {
            let definition = checked.define(
                &constructor.name,
                None,
                &Expr::Core(checked.kernel.data_constructor_function(id, c)?),
            )?;
            exports.push((constructor.name.clone(), definition));
        }
        *self = checked;
        Ok(exports)
    }
    pub fn data_eliminator(&self, id: u64, level: u32) -> Result<Expr, Error> {
        Ok(Expr::Core(self.kernel.data_eliminator_function(id, level)?))
    }
}
