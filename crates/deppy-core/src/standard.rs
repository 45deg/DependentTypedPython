//! Checked standard declarations and compatibility term builders. These use
//! the same declaration validator and eliminator as user-defined families.
use crate::{ConstructorDecl, DataDecl, DataOp, Error, Kernel, Term, Tm};
pub const NAT: u64 = u64::MAX - 2;
pub const VEC: u64 = u64::MAX - 1;
pub const FIN: u64 = u64::MAX;
pub fn vector_id(level: u32) -> u64 {
    VEC - 2 * u64::from(level)
}
pub fn vector_level(id: u64) -> Option<u32> {
    let offset = VEC.checked_sub(id)?;
    (offset % 2 == 0)
        .then_some(offset / 2)
        .and_then(|n| n.try_into().ok())
}
fn carrier_level(ty: &Tm) -> u32 {
    match ty.as_ref() {
        Term::Universe(level) => level.saturating_add(1),
        _ => 0,
    }
}
pub(crate) fn vector_declaration(level: u32) -> DataDecl {
    let v = |i| Term::Var(i).arc();
    DataDecl {
        parameters: vec![Term::Universe(level).arc()],
        indices: vec![Term::Nat.arc()],
        level,
        constructors: vec![
            ConstructorDecl {
                fields: vec![],
                indices: vec![Term::Zero.arc()],
            },
            ConstructorDecl {
                fields: vec![
                    Term::Nat.arc(),
                    v(1),
                    data(DataOp::Type(vector_id(level)), vec![v(2), v(1)]).arc(),
                ],
                indices: vec![Term::Succ(v(2)).arc()],
            },
        ],
    }
}
fn data(op: DataOp, arguments: Vec<Tm>) -> Term {
    Term::Data { op, arguments }
}
#[allow(non_snake_case, non_upper_case_globals)]
impl Term {
    pub const Nat: Self = Self::Data {
        op: DataOp::Type(NAT),
        arguments: Vec::new(),
    };
    pub const Zero: Self = Self::Data {
        op: DataOp::Constructor(NAT, 0),
        arguments: Vec::new(),
    };
    pub fn Succ(n: Tm) -> Self {
        data(DataOp::Constructor(NAT, 1), vec![n])
    }
    pub fn Vec(ty: Tm, len: Tm) -> Self {
        data(DataOp::Type(vector_id(carrier_level(&ty))), vec![ty, len])
    }
    pub fn VNil(ty: Tm) -> Self {
        data(
            DataOp::Constructor(vector_id(carrier_level(&ty)), 0),
            vec![ty],
        )
    }
    pub fn VCons(ty: Tm, len: Tm, head: Tm, tail: Tm) -> Self {
        data(
            DataOp::Constructor(vector_id(carrier_level(&ty)), 1),
            vec![ty, len, head, tail],
        )
    }
    pub fn Fin(bound: Tm) -> Self {
        data(DataOp::Type(FIN), vec![bound])
    }
    pub fn FZ(bound: Tm) -> Self {
        data(DataOp::Constructor(FIN, 0), vec![bound])
    }
    pub fn FS(bound: Tm, pred: Tm) -> Self {
        data(DataOp::Constructor(FIN, 1), vec![bound, pred])
    }
    pub fn NatElim(level: u32, motive: Tm, zero: Tm, step: Tm, scrutinee: Tm) -> Self {
        data(
            DataOp::Eliminate(NAT, level),
            vec![motive, zero, step, scrutinee],
        )
    }
    pub fn VecElim(
        level: u32,
        ty: Tm,
        motive: Tm,
        nil: Tm,
        cons: Tm,
        len: Tm,
        scrutinee: Tm,
    ) -> Self {
        data(
            DataOp::Eliminate(vector_id(carrier_level(&ty)), level),
            vec![ty, len, motive, nil, cons, scrutinee],
        )
    }
    pub fn FinElim(level: u32, motive: Tm, zero: Tm, step: Tm, bound: Tm, scrutinee: Tm) -> Self {
        data(
            DataOp::Eliminate(FIN, level),
            vec![bound, motive, zero, step, scrutinee],
        )
    }
    pub fn Fin0Elim(ty: Tm, absurd: Tm) -> Self {
        data(DataOp::Absurd(FIN), vec![Self::Zero.arc(), ty, absurd])
    }
}
pub(crate) fn install(kernel: &mut Kernel) -> Result<(), Error> {
    let v = |i| Term::Var(i).arc();
    kernel.declare_data(
        NAT,
        DataDecl {
            parameters: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![
                ConstructorDecl {
                    fields: vec![],
                    indices: vec![],
                },
                ConstructorDecl {
                    fields: vec![Term::Nat.arc()],
                    indices: vec![],
                },
            ],
        },
    )?;
    kernel.declare_data(
        VEC,
        DataDecl {
            parameters: vec![Term::Universe(0).arc()],
            indices: vec![Term::Nat.arc()],
            level: 0,
            constructors: vec![
                ConstructorDecl {
                    fields: vec![],
                    indices: vec![Term::Zero.arc()],
                },
                ConstructorDecl {
                    fields: vec![Term::Nat.arc(), v(1), Term::Vec(v(2), v(1)).arc()],
                    indices: vec![Term::Succ(v(2)).arc()],
                },
            ],
        },
    )?;
    kernel.declare_data(
        FIN,
        DataDecl {
            parameters: vec![],
            indices: vec![Term::Nat.arc()],
            level: 0,
            constructors: vec![
                ConstructorDecl {
                    fields: vec![Term::Nat.arc()],
                    indices: vec![Term::Succ(v(0)).arc()],
                },
                ConstructorDecl {
                    fields: vec![Term::Nat.arc(), Term::Fin(v(0)).arc()],
                    indices: vec![Term::Succ(v(1)).arc()],
                },
            ],
        },
    )?;
    Ok(())
}
