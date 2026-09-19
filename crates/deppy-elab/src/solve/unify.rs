use super::*;

impl State {
    pub(super) fn unify(&mut self, a: &T, b: &T) -> Result<(), Error> {
        self.tick()?;
        let a = self.whnf(a)?;
        let b = self.whnf(b)?;
        if a == b {
            return Ok(());
        }
        match (a.as_ref(), b.as_ref()) {
            (
                Term::Data { op, arguments },
                Term::Data {
                    op: other,
                    arguments: right,
                },
            ) if op == other && arguments.len() == right.len() => {
                for (a, b) in arguments.iter().zip(right) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (
                Term::Sigma { id, domain, body },
                Term::Sigma {
                    id: id2,
                    domain: d2,
                    body: b2,
                },
            ) => {
                self.unify(domain, d2)?;
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                let b2 = self.replace(b2, *id2, x)?;
                self.unify(&body, &b2)
            }
            (
                Term::Pair { ty, fst, snd },
                Term::Pair {
                    ty: t2,
                    fst: f2,
                    snd: s2,
                },
            ) => {
                self.unify(ty, t2)?;
                self.unify(fst, f2)?;
                self.unify(snd, s2)
            }
            (Term::Fst(a), Term::Fst(b)) | (Term::Snd(a), Term::Snd(b)) => self.unify(a, b),
            (
                Term::Inductive { id, parameters },
                Term::Inductive {
                    id: id2,
                    parameters: parameters2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (
                Term::Constructor {
                    id,
                    parameters,
                    fields,
                },
                Term::Constructor {
                    id: id2,
                    parameters: parameters2,
                    fields: fields2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                if fields.len() != fields2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in fields.iter().zip(fields2) {
                    self.unify(a, b)?;
                }
                Ok(())
            }
            (
                Term::Elim {
                    id,
                    parameters,
                    level,
                    motive,
                    branch,
                    scrutinee,
                },
                Term::Elim {
                    id: id2,
                    parameters: parameters2,
                    level: level2,
                    motive: motive2,
                    branch: branch2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if id != id2 {
                    return Err(Error::CannotUnify);
                }
                if parameters.len() != parameters2.len() {
                    return Err(Error::CannotUnify);
                }
                for (a, b) in parameters.iter().zip(parameters2) {
                    self.unify(a, b)?;
                }
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(motive, motive2)?;
                self.unify(branch, branch2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (Term::Meta(id, args), _) => self.solve(*id, args, &b),
            (_, Term::Meta(id, args)) => self.solve(*id, args, &a),
            (
                Term::Pi {
                    id,
                    plicity,
                    domain,
                    body,
                },
                Term::Pi {
                    id: id2,
                    plicity: p2,
                    domain: d2,
                    body: b2,
                },
            )
            | (
                Term::Lam {
                    id,
                    plicity,
                    domain,
                    body,
                },
                Term::Lam {
                    id: id2,
                    plicity: p2,
                    domain: d2,
                    body: b2,
                },
            ) => {
                if plicity != p2 {
                    return Err(Error::PlicityMismatch);
                }
                self.unify(domain, d2)?;
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                let b2 = self.replace(b2, *id2, x)?;
                self.unify(&body, &b2)
            }
            (
                Term::Eq { ty, left, right },
                Term::Eq {
                    ty: ty2,
                    left: left2,
                    right: right2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(left, left2)?;
                self.unify(right, right2)?;
                Ok(())
            }
            (
                Term::Refl { ty, value },
                Term::Refl {
                    ty: ty2,
                    value: value2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(value, value2)?;
                Ok(())
            }
            (
                Term::J {
                    level,
                    ty,
                    left,
                    motive,
                    base,
                    right,
                    proof,
                },
                Term::J {
                    level: level2,
                    ty: ty2,
                    left: left2,
                    motive: motive2,
                    base: base2,
                    right: right2,
                    proof: proof2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(ty, ty2)?;
                self.unify(left, left2)?;
                self.unify(motive, motive2)?;
                self.unify(base, base2)?;
                self.unify(right, right2)?;
                self.unify(proof, proof2)?;
                Ok(())
            }
            (Term::Vec { ty, len }, Term::Vec { ty: ty2, len: len2 }) => {
                self.unify(ty, ty2)?;
                self.unify(len, len2)?;
                Ok(())
            }
            (Term::VNil { ty }, Term::VNil { ty: ty2 }) => {
                self.unify(ty, ty2)?;
                Ok(())
            }
            (
                Term::VCons {
                    ty,
                    len,
                    head,
                    tail,
                },
                Term::VCons {
                    ty: ty2,
                    len: len2,
                    head: head2,
                    tail: tail2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(len, len2)?;
                self.unify(head, head2)?;
                self.unify(tail, tail2)?;
                Ok(())
            }
            (Term::Fin { bound }, Term::Fin { bound: bound2 }) => {
                self.unify(bound, bound2)?;
                Ok(())
            }
            (Term::FZ { bound }, Term::FZ { bound: bound2 }) => {
                self.unify(bound, bound2)?;
                Ok(())
            }
            (
                Term::FS { bound, pred },
                Term::FS {
                    bound: bound2,
                    pred: pred2,
                },
            ) => {
                self.unify(bound, bound2)?;
                self.unify(pred, pred2)?;
                Ok(())
            }
            (
                Term::VecElim {
                    level,
                    ty,
                    motive,
                    nil,
                    cons,
                    len,
                    scrutinee,
                },
                Term::VecElim {
                    level: level2,
                    ty: ty2,
                    motive: motive2,
                    nil: nil2,
                    cons: cons2,
                    len: len2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(ty, ty2)?;
                self.unify(motive, motive2)?;
                self.unify(nil, nil2)?;
                self.unify(cons, cons2)?;
                self.unify(len, len2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (
                Term::FinElim {
                    level,
                    motive,
                    zero,
                    step,
                    bound,
                    scrutinee,
                },
                Term::FinElim {
                    level: level2,
                    motive: motive2,
                    zero: zero2,
                    step: step2,
                    bound: bound2,
                    scrutinee: scrutinee2,
                },
            ) => {
                if level != level2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(motive, motive2)?;
                self.unify(zero, zero2)?;
                self.unify(step, step2)?;
                self.unify(bound, bound2)?;
                self.unify(scrutinee, scrutinee2)?;
                Ok(())
            }
            (
                Term::Fin0Elim { ty, absurd },
                Term::Fin0Elim {
                    ty: ty2,
                    absurd: absurd2,
                },
            ) => {
                self.unify(ty, ty2)?;
                self.unify(absurd, absurd2)?;
                Ok(())
            }
            (Term::Succ(x), Term::Succ(y)) => self.unify(x, y),
            (
                Term::NatElim {
                    level: l,
                    motive: p,
                    zero: z,
                    step: s,
                    scrutinee: n,
                },
                Term::NatElim {
                    level: l2,
                    motive: p2,
                    zero: z2,
                    step: s2,
                    scrutinee: n2,
                },
            ) => {
                if l != l2 {
                    return Err(Error::CannotUnify);
                }
                self.unify(p, p2)?;
                self.unify(z, z2)?;
                self.unify(s, s2)?;
                self.unify(n, n2)
            }
            (Term::App(f, x), Term::App(g, y)) => {
                self.unify(f, g)?;
                self.unify(x, y)
            }
            // Eta only for lambda versus a neutral term. No general search.
            (
                Term::Lam { id, body, .. },
                Term::Local(_)
                | Term::App(_, _)
                | Term::NatElim { .. }
                | Term::J { .. }
                | Term::VecElim { .. }
                | Term::FinElim { .. }
                | Term::Fst(_)
                | Term::Snd(_)
                | Term::Elim { .. }
                | Term::Fin0Elim { .. },
            ) => {
                let x = Term::Local(self.fresh()).arc();
                let body = self.replace(body, *id, x.clone())?;
                self.unify(&body, &Term::App(b.clone(), x).arc())
            }
            (
                Term::Local(_)
                | Term::App(_, _)
                | Term::NatElim { .. }
                | Term::J { .. }
                | Term::VecElim { .. }
                | Term::FinElim { .. }
                | Term::Fst(_)
                | Term::Snd(_)
                | Term::Elim { .. }
                | Term::Fin0Elim { .. },
                Term::Lam { .. },
            ) => self.unify(&b, &a),
            _ => Err(Error::CannotUnify),
        }
    }

    fn solve(&mut self, id: Id, args: &[T], rhs: &T) -> Result<(), Error> {
        // Only contextual pattern spines, with distinct variables, are solved.
        let telescope = self.metas[id].telescope.clone();
        let mut rename = HashMap::new();
        for (arg, local) in args.iter().zip(&telescope) {
            let arg = self.whnf(arg)?;
            let Term::Local(arg_id) = arg.as_ref() else {
                return Err(Error::NonPattern);
            };
            if rename
                .insert(*arg_id, Term::Local(local.id).arc())
                .is_some()
            {
                return Err(Error::NonPattern);
            }
        }
        let rhs = self.zonk(rhs)?;
        self.validate_solution(id, &rhs, &mut rename.keys().copied().collect())?;
        let solution = self.subst(&rhs, &rename)?;
        self.metas[id].solution = Some(solution);
        Ok(())
    }

    pub(super) fn validate_solution(
        &mut self,
        solving: Id,
        term: &T,
        allowed: &mut HashSet<Id>,
    ) -> Result<(), Error> {
        self.tick()?;
        match term.as_ref() {
            Term::Data {
                arguments: parameters,
                ..
            }
            | Term::Inductive { parameters, .. } => {
                for child in parameters {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Constructor {
                parameters, fields, ..
            } => {
                for child in parameters.iter().chain(fields) {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Elim {
                parameters,
                motive,
                branch,
                scrutinee,
                ..
            } => {
                for child in parameters.iter().chain([motive, branch, scrutinee]) {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fst(p) | Term::Snd(p) => self.validate_solution(solving, p, allowed),
            Term::Pair { ty, fst, snd } => {
                for child in [ty, fst, snd] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Local(id) if !allowed.contains(id) => Err(Error::ScopeEscape),
            Term::Global(_) | Term::Local(_) | Term::Universe(_) | Term::Nat | Term::Zero => Ok(()),
            Term::Eq {
                ty, left, right, ..
            } => {
                for child in [ty, left, right] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Refl { ty, value, .. } => {
                for child in [ty, value] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::J {
                ty,
                left,
                motive,
                base,
                right,
                proof,
                ..
            } => {
                for child in [ty, left, motive, base, right, proof] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Vec { ty, len, .. } => {
                for child in [ty, len] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::VNil { ty, .. } => {
                self.validate_solution(solving, ty, allowed)?;
                Ok(())
            }
            Term::VCons {
                ty,
                len,
                head,
                tail,
                ..
            } => {
                for child in [ty, len, head, tail] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fin { bound, .. } => {
                self.validate_solution(solving, bound, allowed)?;
                Ok(())
            }
            Term::FZ { bound, .. } => {
                self.validate_solution(solving, bound, allowed)?;
                Ok(())
            }
            Term::FS { bound, pred, .. } => {
                for child in [bound, pred] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::VecElim {
                ty,
                motive,
                nil,
                cons,
                len,
                scrutinee,
                ..
            } => {
                for child in [ty, motive, nil, cons, len, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::FinElim {
                motive,
                zero,
                step,
                bound,
                scrutinee,
                ..
            } => {
                for child in [motive, zero, step, bound, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Fin0Elim { ty, absurd, .. } => {
                for child in [ty, absurd] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Succ(n) => self.validate_solution(solving, n, allowed),
            Term::NatElim {
                motive,
                zero,
                step,
                scrutinee,
                ..
            } => {
                for child in [motive, zero, step, scrutinee] {
                    self.validate_solution(solving, child, allowed)?;
                }
                Ok(())
            }
            Term::Meta(id, _) if *id == solving => Err(Error::OccursCheck),
            Term::Meta(_, args) => {
                for arg in args {
                    self.validate_solution(solving, arg, allowed)?;
                }
                Ok(())
            }
            Term::App(f, x) => {
                self.validate_solution(solving, f, allowed)?;
                self.validate_solution(solving, x, allowed)
            }
            Term::Sigma { id, domain, body }
            | Term::Pi {
                id, domain, body, ..
            }
            | Term::Lam {
                id, domain, body, ..
            } => {
                self.validate_solution(solving, domain, allowed)?;
                let inserted = allowed.insert(*id);
                let result = self.validate_solution(solving, body, allowed);
                if inserted {
                    allowed.remove(id);
                }
                result
            }
        }
    }
}
