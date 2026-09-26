//! Resolve contextual integer literals before ANF introduces unannotated temps.
//! This pass only selects literal representations; value() still checks every
//! expression and rejects implicit conversions of existing Nat/Bool values.
use super::*;
impl Lowerer {
    fn integer_context(&self, expression: &mut Expr, state: &State, expected: Option<Scalar>) {
        match expression {
            Expr::NumberLiteral(_) if expected == Some(Scalar::Int) => {
                *expression = range::call("$int_literal", vec![expression.clone()], expression);
            }
            Expr::BinOp(b) => {
                let ty = self.numeric_type(&b.left, &b.right, state, expected);
                self.integer_context(&mut b.left, state, Some(ty));
                self.integer_context(&mut b.right, state, Some(ty));
            }
            Expr::UnaryOp(u) => {
                self.integer_context(
                    &mut u.operand,
                    state,
                    Some(if u.op == ast::UnaryOp::USub {
                        Scalar::Int
                    } else {
                        Scalar::Bool
                    }),
                );
            }
            Expr::Compare(c) if c.comparators.len() == 1 => {
                let ty = self.numeric_type(&c.left, &c.comparators[0], state, None);
                self.integer_context(&mut c.left, state, Some(ty));
                self.integer_context(&mut c.comparators[0], state, Some(ty));
            }
            Expr::If(i) => {
                self.integer_context(&mut i.test, state, Some(Scalar::Bool));
                self.integer_context(&mut i.body, state, expected);
                self.integer_context(&mut i.orelse, state, expected);
            }
            Expr::BoolOp(b) => {
                for value in &mut b.values {
                    self.integer_context(value, state, Some(Scalar::Bool));
                }
            }
            Expr::Call(c) => {
                let parameters = if let Expr::Name(n) = c.func.as_ref() {
                    self.globals
                        .get(n.id.as_str())
                        .and_then(|b| b.contract.as_ref())
                        .map(|c| &c.parameters)
                } else {
                    None
                };
                for (i, argument) in c.arguments.args.iter_mut().enumerate() {
                    self.integer_context(
                        argument,
                        state,
                        parameters.and_then(|p| p.get(i)).copied(),
                    );
                }
            }
            _ => {}
        }
    }

    pub(super) fn numeric_context(
        &self,
        body: &mut [Stmt],
        state: &mut State,
        result: Scalar,
    ) -> Result<(), Diagnostic> {
        for statement in body {
            match statement {
                Stmt::Assign(a) if a.targets.len() == 1 => {
                    match (&a.targets[0], a.value.as_mut()) {
                        (Expr::Name(n), value) => {
                            let expected = state.types.get(n.id.as_str()).copied();
                            self.integer_context(value, state, expected);
                            let ty = expected
                                .or_else(|| self.numeric_hint(value, state))
                                .unwrap_or(Scalar::Nat);
                            state.types.insert(n.id.to_string(), ty);
                        }
                        (Expr::Tuple(targets), Expr::Tuple(values)) => {
                            let mut types = vec![];
                            for (target, value) in targets.elts.iter().zip(&mut values.elts) {
                                if let Expr::Name(n) = target {
                                    let expected = state.types.get(n.id.as_str()).copied();
                                    self.integer_context(value, state, expected);
                                    types.push((
                                        n.id.to_string(),
                                        expected
                                            .or_else(|| self.numeric_hint(value, state))
                                            .unwrap_or(Scalar::Nat),
                                    ));
                                }
                            }
                            state.types.extend(types);
                        }
                        _ => {}
                    }
                }
                Stmt::AnnAssign(a) => {
                    if let Expr::Name(n) = a.target.as_ref() {
                        let base = self
                            .refinement(&a.annotation)?
                            .map_or(a.annotation.as_ref(), |(b, _)| b);
                        let ty = self.scalar(base)?;
                        if let Some(value) = &mut a.value {
                            self.integer_context(value, state, Some(ty));
                        }
                        state.types.insert(n.id.to_string(), ty);
                    }
                }
                Stmt::AugAssign(a) => {
                    let expected = self.numeric_hint(&a.target, state);
                    self.integer_context(&mut a.value, state, expected);
                }
                Stmt::Return(r) => {
                    if let Some(value) = &mut r.value {
                        self.integer_context(value, state, Some(result));
                    }
                }
                Stmt::Assert(a) => self.integer_context(&mut a.test, state, Some(Scalar::Bool)),
                Stmt::If(i) => {
                    self.integer_context(&mut i.test, state, Some(Scalar::Bool));
                    let mut arms = vec![];
                    let mut yes = state.clone();
                    self.numeric_context(&mut i.body, &mut yes, result)?;
                    arms.push(yes);
                    for clause in &mut i.elif_else_clauses {
                        if let Some(test) = &mut clause.test {
                            self.integer_context(test, state, Some(Scalar::Bool));
                        }
                        let mut branch = state.clone();
                        self.numeric_context(&mut clause.body, &mut branch, result)?;
                        arms.push(branch);
                    }
                    if !i.elif_else_clauses.last().is_some_and(|c| c.test.is_none()) {
                        arms.push(state.clone());
                    }
                    state.types = arms[0]
                        .types
                        .iter()
                        .filter(|(name, ty)| arms.iter().all(|s| s.types.get(*name) == Some(*ty)))
                        .map(|(n, t)| (n.clone(), *t))
                        .collect();
                }
                Stmt::While(w) => {
                    self.integer_context(&mut w.test, state, Some(Scalar::Bool));
                    self.numeric_context(&mut w.body, &mut state.clone(), result)?;
                }
                Stmt::For(f) => {
                    // Range still accepts Nat bounds and a literal negative step.
                    self.numeric_context(&mut f.body, &mut state.clone(), result)?;
                }
                _ => {}
            }
        }
        Ok(())
    }
}
