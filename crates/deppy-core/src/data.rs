//! General strictly positive indexed inductive families.
use crate::Tm;

/// The arguments of every operation are ordered by its declaration's telescopes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DataOp {
    Type(u64),
    Absurd(u64),
    Constructor(u64, usize),
    /// Parameters, indices, motive, one branch per constructor, scrutinee.
    Eliminate(u64, u32),
}
impl DataOp {
    pub fn id(self) -> u64 {
        match self {
            Self::Type(id)
            | Self::Absurd(id)
            | Self::Constructor(id, _)
            | Self::Eliminate(id, _) => id,
        }
    }
}
#[derive(Clone, Debug)]
pub struct ConstructorDecl {
    /// Scoped over the parameters and preceding fields.
    pub fields: Vec<Tm>,
    /// Result indices, scoped over parameters and all fields.
    pub indices: Vec<Tm>,
}
#[derive(Clone, Debug)]
pub struct DataDecl {
    pub parameters: Vec<Tm>,
    /// Scoped over parameters and preceding indices.
    pub indices: Vec<Tm>,
    pub constructors: Vec<ConstructorDecl>,
    pub level: u32,
}
