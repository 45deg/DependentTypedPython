use super::*;

impl Lowerer {
    pub(super) fn refinement<'a>(
        &self,
        annotation: &'a Expr,
    ) -> Result<Option<(&'a Expr, &'a Expr)>, Diagnostic> {
        if let Expr::Subscript(subscript) = annotation {
            if self.builtin(&subscript.value, &Scope::default()) == Some("Refined") {
                if let Expr::Tuple(arguments) = subscript.slice.as_ref() {
                    if arguments.elts.len() == 2 {
                        return Ok(Some((&arguments.elts[0], &arguments.elts[1])));
                    }
                }
                return Err(error(annotation, "use Refined[base, predicate]"));
            }
        }
        Ok(None)
    }

    pub(super) fn scalar(&self, e: &Expr) -> Result<Scalar, Diagnostic> {
        if self.builtin(e, &Scope::default()) == Some("Nat") {
            return Ok(Scalar::Nat);
        }
        if let Expr::Name(n) = e {
            if self
                .globals
                .get(n.id.as_str())
                .is_some_and(|b| b.name == "deppy.integer.Int")
            {
                return Ok(Scalar::Int);
            }
            if self
                .globals
                .get(n.id.as_str())
                .is_some_and(|b| b.name == "deppy.data.Bool")
            {
                return Ok(Scalar::Bool);
            }
        }
        Err(error(
            e,
            "verified values require Nat, deppy.data.Bool, or deppy.integer.Int",
        ))
    }

    pub(super) fn commands<'a>(
        &mut self,
        body: &'a [Stmt],
    ) -> Result<Vec<Command<'a>>, Diagnostic> {
        let mut commands = vec![];
        for statement in body {
            self.tick(statement.range())?;
            let command =
                match statement {
                    Stmt::Assign(a) if a.targets.len() == 1 => {
                        match (&a.targets[0], a.value.as_ref()) {
                        (Expr::Name(n), _) => Command::Assign(n.id.as_str(), None, &a.value),
                        (Expr::Tuple(targets), Expr::Tuple(values)) if !targets.elts.is_empty() && targets.elts.len() == values.elts.len() => {
                            let mut bindings = vec![];
                            let mut seen = HashSet::new();
                            for (target, value) in targets.elts.iter().zip(&values.elts) {
                                let Expr::Name(n) = target else {
                                    return Err(error(target, "parallel assignment requires distinct local names"));
                                };
                                if !seen.insert(n.id.as_str()) {
                                    return Err(error(target, "parallel assignment requires distinct local names"));
                                }
                                bindings.push((n.id.as_str(), value));
                            }
                            Command::Parallel(bindings)
                        }
                        _ => return Err(error(a, "verified assignment requires a local name or equal-length tuples of local names and values")),
                    }
                    }
                    Stmt::AnnAssign(a) => {
                        let Expr::Name(n) = a.target.as_ref() else {
                            return Err(error(a, "verified assignment requires one local name"));
                        };
                        let scalar =
                            if let Some((base, predicate)) = self.refinement(&a.annotation)? {
                                let scalar = self.scalar(base)?;
                                commands.push(Command::Refine(n.id.as_str(), scalar, predicate));
                                scalar
                            } else {
                                self.scalar(&a.annotation)?
                            };
                        Command::Assign(
                            n.id.as_str(),
                            Some(scalar),
                            a.value
                                .as_deref()
                                .ok_or_else(|| error(a, "verified local requires a value"))?,
                        )
                    }
                    Stmt::If(branch) => {
                        let mut otherwise = vec![];
                        for clause in branch.elif_else_clauses.iter().rev() {
                            let body = self.commands(&clause.body)?;
                            otherwise = if let Some(test) = &clause.test {
                                vec![Command::If(test, body, otherwise)]
                            } else {
                                body
                            };
                        }
                        Command::If(&branch.test, self.commands(&branch.body)?, otherwise)
                    }
                    Stmt::Assert(a) if a.msg.is_none() => Command::Assert(&a.test),
                    Stmt::Break(b) => Command::Break(b),
                    Stmt::Continue(c) => Command::Continue(c),
                    Stmt::While(w) => Command::While(self.loop_command(w)?),
                    Stmt::Return(r) => Command::Return(
                        r.value
                            .as_deref()
                            .ok_or_else(|| error(r, "verified return requires a value"))?,
                    ),
                    _ => {
                        return Err(error(
                            statement,
                            "verified supports local assignment, if, while, and return",
                        ))
                    }
                };
            commands.push(command);
        }
        Ok(commands)
    }
}
