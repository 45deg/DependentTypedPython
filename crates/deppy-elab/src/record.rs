use crate::{Elaborator, Error, Expr, Plicity};
use deppy_core::{InductiveDecl, InductiveId, Term};
use std::collections::HashSet;
/// Named telescope. Field types can refer to parameters and preceding fields.
/// Parameters become implicit arguments; fields remain explicit runtime values.
#[derive(Clone, Debug)]
pub struct RecordDecl {
    pub parameters: Vec<(String, Expr)>,
    pub fields: Vec<(String, Expr)>,
    pub level: u32,
}
#[derive(Clone, Debug)]
pub struct Record {
    pub id: InductiveId,
    ty: Expr,
    constructor: Expr,
    projections: Vec<(String, Expr)>,
}
impl Record {
    /// Apply parameters with `.implicit(...)` when using this type expression.
    pub fn ty(&self) -> Expr {
        self.ty.clone()
    }
    pub fn constructor(&self) -> Expr {
        self.constructor.clone()
    }
    /// Projection function; implicit parameters are inferred from its record argument.
    pub fn projection(&self, name: &str) -> Result<Expr, Error> {
        self.projections
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, p)| p.clone())
            .ok_or_else(|| Error::UnknownName(name.into()))
    }
}
impl Elaborator {
    /// Atomically check and register a nominal nonrecursive dependent record.
    pub fn declare_record(&mut self, id: InductiveId, decl: RecordDecl) -> Result<Record, Error> {
        let mut names = HashSet::new();
        for (name, _) in decl.parameters.iter().chain(&decl.fields) {
            if name.is_empty() || !names.insert(name) {
                return Err(Error::InvalidDeclarationName(name.clone()));
            }
        }
        let telescope = decl
            .parameters
            .iter()
            .chain(&decl.fields)
            .collect::<Vec<_>>();
        let signature = telescope
            .iter()
            .rev()
            .fold(Expr::Universe(0), |body, (name, ty)| {
                Expr::pi(name.clone(), Plicity::Explicit, ty.clone(), body)
            });
        let mut checked = self.infer(&signature)?.term;
        let mut types = vec![];
        for _ in &telescope {
            let Term::Pi {
                domain, codomain, ..
            } = checked.as_ref()
            else {
                return Err(Error::ExpectedFunction);
            };
            types.push(domain.clone());
            checked = codomain.clone();
        }
        let fields = types.split_off(decl.parameters.len());
        let mut kernel = self.kernel.clone();
        kernel.declare(
            id,
            InductiveDecl {
                parameters: types,
                fields,
                level: decl.level,
            },
        )?;
        let ty = Expr::Core(kernel.inductive_function(id)?);
        let constructor = Expr::Core(kernel.constructor_function(id)?);
        let projections = decl
            .fields
            .into_iter()
            .zip(kernel.projection_functions(id)?)
            .map(|((name, _), p)| (name, Expr::Core(p)))
            .collect();
        self.kernel = kernel;
        let record = Record {
            id,
            ty,
            constructor,
            projections,
        };
        self.records.insert(id, record.clone());
        Ok(record)
    }
}
