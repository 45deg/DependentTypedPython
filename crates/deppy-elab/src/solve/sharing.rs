//! Syntactic support summaries preserve DAG sharing during substitution.
use super::*;
use std::sync::Arc;

impl State {
    pub(super) fn free_locals(&mut self, term: &T) -> Result<Arc<HashSet<Id>>, Error> {
        self.tick()?;
        let key = Arc::as_ptr(term) as usize;
        if let Some((_, ids)) = self.support.get(&key) {
            return Ok(ids.clone());
        }
        let mut ids = HashSet::new();
        let children: Vec<&T> = match term.as_ref() {
            Term::Defined { id, value } => {
                ids.insert(*id);
                vec![value]
            }
            Term::Local(id) => {
                ids.insert(*id);
                vec![]
            }
            Term::Global(_) | Term::Universe(_) | Term::Nat | Term::Zero => vec![],
            Term::Data { arguments, .. } | Term::Meta(_, arguments) => arguments.iter().collect(),
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
                id, domain, body, ..
            }
            | Term::Lam {
                id, domain, body, ..
            }
            | Term::Sigma { id, domain, body } => {
                ids.extend(self.free_locals(body)?.iter().filter(|x| *x != id));
                vec![domain]
            }
            Term::Fst(x) | Term::Snd(x) | Term::Succ(x) => vec![x],
            Term::Pair { ty, fst, snd } => vec![ty, fst, snd],
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
            Term::Vec { ty, len } => vec![ty, len],
            Term::VNil { ty } => vec![ty],
            Term::VCons {
                ty,
                len,
                head,
                tail,
            } => vec![ty, len, head, tail],
            Term::Fin { bound } | Term::FZ { bound } => vec![bound],
            Term::FS { bound, pred } => vec![bound, pred],
            Term::VecElim {
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
                ..
            } => vec![ty, motive, nil, cons, len, scrutinee],
            Term::FinElim {
                motive,
                zero,
                step,
                bound,
                scrutinee,
                ..
            } => vec![motive, zero, step, bound, scrutinee],
            Term::Fin0Elim { ty, absurd } => vec![ty, absurd],
            Term::NatElim {
                motive,
                zero,
                step,
                scrutinee,
                ..
            } => vec![motive, zero, step, scrutinee],
            Term::App(f, x) => vec![f, x],
        };
        for child in children {
            ids.extend(self.free_locals(child)?.iter());
        }
        let ids = Arc::new(ids);
        // Retain the key's allocation to prevent pointer reuse, with bounded storage.
        if self.support.len() >= 16_384 {
            self.support.clear();
        }
        self.support.insert(key, (term.clone(), ids.clone()));
        Ok(ids)
    }
}
