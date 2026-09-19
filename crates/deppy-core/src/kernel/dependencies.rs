use super::*;
use std::collections::BTreeSet;

impl Kernel {
    /// All explicit assumptions used by a checked term, including its type,
    /// annotations, referenced definitions and nominal record declarations.
    /// This is syntactic dependency tracking, not proof minimization.
    pub fn axiom_dependencies(&self, term: &Tm) -> Result<BTreeSet<crate::DefId>, Error> {
        let ty = self.infer(term)?;
        let mut pending = vec![term.clone(), ty];
        let mut definitions = BTreeSet::new();
        let mut records = BTreeSet::new();
        let mut families = BTreeSet::new();
        let mut axioms = BTreeSet::new();
        let mut remaining = self.max_steps;
        while let Some(term) = pending.pop() {
            remaining = remaining.checked_sub(1).ok_or(Error::BudgetExceeded)?;
            match term.as_ref() {
                Term::Data { op, arguments } => {
                    pending.extend(arguments.iter().cloned());
                    if families.insert(op.id()) {
                        let decl = self.data_declaration(op.id())?;
                        pending.extend(decl.parameters.iter().chain(&decl.indices).cloned());
                        for ctor in &decl.constructors {
                            pending.extend(ctor.fields.iter().chain(&ctor.indices).cloned());
                        }
                    }
                }
                Term::Global(id) => {
                    if definitions.insert(*id) {
                        let declaration = self.definition(*id)?;
                        pending.push(declaration.ty.clone());
                        if let Some(body) = &declaration.body {
                            pending.push(body.clone());
                        } else {
                            axioms.insert(*id);
                        }
                    }
                }
                Term::Inductive { id, parameters }
                | Term::Constructor { id, parameters, .. }
                | Term::Elim { id, parameters, .. } => {
                    pending.extend(parameters.iter().cloned());
                    if records.insert(*id) {
                        let declaration = self.declaration(*id)?;
                        pending.extend(declaration.parameters.iter().cloned());
                        pending.extend(declaration.fields.iter().cloned());
                    }
                    match term.as_ref() {
                        Term::Constructor { fields, .. } => pending.extend(fields.iter().cloned()),
                        Term::Elim {
                            motive,
                            branch,
                            scrutinee,
                            ..
                        } => pending.extend([motive.clone(), branch.clone(), scrutinee.clone()]),
                        _ => {}
                    }
                }
                Term::Sigma { domain, codomain }
                | Term::Pi {
                    domain, codomain, ..
                } => pending.extend([domain.clone(), codomain.clone()]),
                Term::Lam { domain, body, .. } => pending.extend([domain.clone(), body.clone()]),
                Term::Pair { ty, fst, snd } => {
                    pending.extend([ty.clone(), fst.clone(), snd.clone()])
                }
                Term::Fst(t) | Term::Snd(t) => pending.push(t.clone()),
                Term::Eq { ty, left, right } => {
                    pending.extend([ty.clone(), left.clone(), right.clone()])
                }
                Term::Refl { ty, value } => pending.extend([ty.clone(), value.clone()]),
                Term::J {
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                    ..
                } => pending.extend([
                    ty.clone(),
                    left.clone(),
                    motive.clone(),
                    base.clone(),
                    right.clone(),
                    proof.clone(),
                ]),

                Term::App { function, argument } => {
                    pending.extend([function.clone(), argument.clone()])
                }
                Term::Let { ty, value, body } => {
                    pending.extend([ty.clone(), value.clone(), body.clone()])
                }
                Term::Var(_) | Term::Universe(_) => {}
            }
        }
        Ok(axioms)
    }
}
