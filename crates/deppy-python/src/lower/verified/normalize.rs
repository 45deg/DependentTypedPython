//! A-normalization preserves source ranges and Python's left-to-right order.
//! Generated names contain `$`, which cannot occur in a source identifier.
use super::*;

pub(super) fn assign(target: Expr, value: Expr) -> Stmt {
    Stmt::Assign(ast::StmtAssign {
        node_index: Default::default(),
        range: value.range(),
        targets: vec![target],
        value: Box::new(value),
    })
}
fn branch(test: Expr, yes: Vec<Stmt>, no: Vec<Stmt>) -> Stmt {
    Stmt::If(ast::StmtIf {
        node_index: Default::default(),
        range: test.range(),
        test: Box::new(test.clone()),
        body: yes.into_iter().collect(),
        elif_else_clauses: vec![ast::ElifElseClause {
            node_index: Default::default(),
            range: test.range(),
            test: None,
            body: no.into_iter().collect(),
        }],
    })
}
impl Lowerer {
    fn temporary(&mut self, source: &Expr) -> Expr {
        let id = self.wildcard;
        self.wildcard += 1;
        Expr::Name(ast::ExprName {
            node_index: Default::default(),
            range: source.range(),
            id: format!("$expr{id}").into(),
            ctx: ast::ExprContext::Load,
        })
    }

    pub(super) fn has_contract_call(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Call(call) => {
                matches!(call.func.as_ref(), Expr::Name(n) if self.globals.get(n.id.as_str()).is_some_and(|b| b.verified))
                    || call
                        .arguments
                        .args
                        .iter()
                        .any(|arg| self.has_contract_call(arg))
            }
            Expr::If(op) => {
                self.has_contract_call(&op.test)
                    || self.has_contract_call(&op.body)
                    || self.has_contract_call(&op.orelse)
            }
            Expr::BoolOp(op) => op.values.iter().any(|e| self.has_contract_call(e)),
            Expr::BinOp(op) => {
                self.has_contract_call(&op.left) || self.has_contract_call(&op.right)
            }
            Expr::Compare(op) => {
                self.has_contract_call(&op.left)
                    || op.comparators.iter().any(|e| self.has_contract_call(e))
            }
            Expr::UnaryOp(op) => self.has_contract_call(&op.operand),
            _ => false,
        }
    }

    pub(super) fn normalize_value(
        &mut self,
        expr: &Expr,
        prefix: &mut Vec<Stmt>,
        root: bool,
    ) -> Result<Expr, Diagnostic> {
        self.tick(expr.range())?;
        let mut value = expr.clone();
        match &mut value {
            Expr::Call(call) => {
                for arg in &mut call.arguments.args {
                    *arg = self.normalize_value(arg, prefix, false)?;
                }
            }
            Expr::BinOp(op) => {
                *op.left = self.normalize_value(&op.left, prefix, false)?;
                *op.right = self.normalize_value(&op.right, prefix, false)?;
            }
            Expr::Compare(op) => {
                *op.left = self.normalize_value(&op.left, prefix, false)?;
                for right in &mut op.comparators {
                    *right = self.normalize_value(right, prefix, false)?;
                }
            }
            Expr::UnaryOp(op) => {
                *op.operand = self.normalize_value(&op.operand, prefix, false)?;
            }
            // Pure selectors remain expressions: their continuation is shared,
            // and value() checks both arms against the same scalar type.
            Expr::If(_) | Expr::BoolOp(_) if !self.has_contract_call(expr) => {}
            Expr::If(op) => {
                let test = self.normalize_value(&op.test, prefix, false)?;
                let target = self.temporary(expr);
                let mut yes = vec![];
                let body = self.normalize_value(&op.body, &mut yes, true)?;
                yes.push(assign(target.clone(), body));
                let mut no = vec![];
                let body = self.normalize_value(&op.orelse, &mut no, true)?;
                no.push(assign(target.clone(), body));
                prefix.push(branch(test, yes, no));
                return Ok(target);
            }
            Expr::BoolOp(op) => {
                // Each operand is checked as Bool by a guard, including the last.
                let target = self.temporary(expr);
                let literal = |value| {
                    Expr::BooleanLiteral(ast::ExprBooleanLiteral {
                        range: expr.range(),
                        value,
                        ..Default::default()
                    })
                };
                let mut tail = vec![assign(target.clone(), literal(op.op == ast::BoolOp::And))];
                for operand in op.values.iter().rev() {
                    let mut before = vec![];
                    let test = self.normalize_value(operand, &mut before, false)?;
                    let stop = vec![assign(target.clone(), literal(op.op == ast::BoolOp::Or))];
                    before.push(if op.op == ast::BoolOp::And {
                        branch(test, tail, stop)
                    } else {
                        branch(test, stop, tail)
                    });
                    tail = before;
                }
                prefix.extend(tail);
                return Ok(target);
            }
            _ => {}
        }
        let contract = matches!(&value, Expr::Call(c) if matches!(c.func.as_ref(), Expr::Name(n) if self.globals.get(n.id.as_str()).is_some_and(|b| b.verified)));
        if contract && !root {
            let name = self.temporary(expr);
            prefix.push(assign(name.clone(), value));
            Ok(name)
        } else {
            Ok(value)
        }
    }

    pub(super) fn normalize_commands(&mut self, body: &[Stmt]) -> Result<Vec<Stmt>, Diagnostic> {
        let mut output = vec![];
        for statement in body {
            self.tick(statement.range())?;
            let mut statement = statement.clone();
            match &mut statement {
                Stmt::Assign(a) => {
                    if let Expr::Tuple(values) = a.value.as_mut() {
                        // Only generated names are written here. The original
                        // parallel command still snapshots every RHS before any
                        // user local changes, retaining its expected scalar type.
                        for value in &mut values.elts {
                            *value = self.normalize_value(value, &mut output, false)?;
                        }
                    } else {
                        *a.value = self.normalize_value(&a.value, &mut output, true)?;
                    }
                }
                Stmt::AnnAssign(a) => {
                    if let Some(value) = &mut a.value {
                        **value = self.normalize_value(value, &mut output, true)?;
                    }
                }
                Stmt::AugAssign(a)
                    if a.op == ast::Operator::Add && matches!(a.target.as_ref(), Expr::Name(_)) =>
                {
                    let value = Expr::BinOp(ast::ExprBinOp {
                        node_index: Default::default(),
                        range: a.range,
                        left: a.target.clone(),
                        op: a.op,
                        right: a.value.clone(),
                    });
                    let value = self.normalize_value(&value, &mut output, true)?;
                    statement = assign(*a.target.clone(), value);
                }
                Stmt::Return(r) => {
                    if let Some(value) = &mut r.value {
                        **value = self.normalize_value(value, &mut output, true)?;
                    }
                }
                Stmt::Assert(a) => {
                    *a.test = self.normalize_value(&a.test, &mut output, false)?;
                }
                Stmt::If(i) => {
                    *i.test = self.normalize_value(&i.test, &mut output, false)?;
                    i.body = self.normalize_commands(&i.body)?.into_iter().collect();
                    let mut tail = vec![];
                    for clause in i.elif_else_clauses.iter().rev() {
                        let body = self.normalize_commands(&clause.body)?;
                        if let Some(test) = &clause.test {
                            let mut before = vec![];
                            let test = self.normalize_value(test, &mut before, false)?;
                            before.push(branch(test, body, tail));
                            tail = before;
                        } else {
                            tail = body;
                        }
                    }
                    i.elif_else_clauses = if tail.is_empty() {
                        vec![]
                    } else {
                        vec![ast::ElifElseClause {
                            node_index: Default::default(),
                            range: i.range,
                            test: None,
                            body: tail.into_iter().collect(),
                        }]
                    };
                }
                Stmt::For(f) => {
                    output.extend(self.normalize_range(f)?);
                    continue;
                }
                Stmt::While(w) => {
                    w.body = self.normalize_commands(&w.body)?.into_iter().collect();
                }
                _ => {}
            }
            output.push(statement);
        }
        Ok(output)
    }
}
