use super::*;

impl Lowerer {
    pub(super) fn value(
        &mut self,
        e: &Expr,
        state: &State,
        expected: Option<Scalar>,
    ) -> Result<(E, Scalar), Diagnostic> {
        self.tick(e.range())?;
        let (term, ty) = match e {
            Expr::BooleanLiteral(b) => (
                E::name(if b.value {
                    "deppy.data.True_"
                } else {
                    "deppy.data.False_"
                }),
                Scalar::Bool,
            ),
            Expr::NumberLiteral(_) => {
                let value = self.expr(e, &state.scope)?;
                if expected == Some(Scalar::Int) {
                    (E::name("deppy.integer.Pos").app(value), Scalar::Int)
                } else {
                    (value, Scalar::Nat)
                }
            }
            Expr::Name(n) => {
                let ty = state
                    .types
                    .get(n.id.as_str())
                    .copied()
                    .ok_or_else(|| error(n, "verified value must be an initialized local"))?;
                (self.expr(e, &state.scope)?, ty)
            }
            Expr::BinOp(b) => {
                let ty = self.numeric_type(&b.left, &b.right, state, expected);
                let name = match (b.op, ty) {
                    (ast::Operator::Add, Scalar::Int) => "deppy.integer.add",
                    (ast::Operator::Mult, Scalar::Int) => "deppy.integer.mul",
                    (ast::Operator::Add, _) => "deppy.nat.add",
                    (ast::Operator::Mult, _) => "deppy.nat.mul",
                    _ => return Err(error(b, "checked arithmetic is unsupported in loop guards or measures; assign it in the body first")),
                };
                let left = self.value(&b.left, state, Some(ty))?.0;
                let right = self.value(&b.right, state, Some(ty))?.0;
                (E::name(name).app(left).app(right), ty)
            }
            Expr::Compare(c) if c.ops.len() == 1 && c.comparators.len() == 1 => {
                let name = match c.ops[0] {
                    ast::CmpOp::Lt => "deppy.verified.nat_lt",
                    ast::CmpOp::LtE => "deppy.verified.nat_le",
                    ast::CmpOp::Gt => "deppy.verified.nat_lt",
                    ast::CmpOp::GtE => "deppy.verified.nat_le",
                    ast::CmpOp::Eq | ast::CmpOp::NotEq => "deppy.verified.nat_eq",
                    _ => {
                        return Err(error(
                            c,
                            "verified comparisons support ==, !=, <, <=, >, and >=",
                        ))
                    }
                };
                let equality = matches!(c.ops[0], ast::CmpOp::Eq | ast::CmpOp::NotEq);
                let (left, ty) = self.value(
                    &c.left,
                    state,
                    if equality
                        && (self.numeric_hint(&c.left, state) == Some(Scalar::Bool)
                            || self.numeric_hint(&c.comparators[0], state) == Some(Scalar::Bool))
                    {
                        Some(Scalar::Bool)
                    } else {
                        Some(self.numeric_type(&c.left, &c.comparators[0], state, None))
                    },
                )?;
                let right = self.value(&c.comparators[0], state, Some(ty))?.0;
                let name = if equality && ty == Scalar::Bool {
                    "deppy.verified.bool_eq"
                } else if ty == Scalar::Int {
                    match c.ops[0] {
                        ast::CmpOp::Lt | ast::CmpOp::Gt => "deppy.integer.lt",
                        ast::CmpOp::LtE | ast::CmpOp::GtE => "deppy.integer.le",
                        _ => "deppy.integer.eq",
                    }
                } else {
                    name
                };
                let term = if matches!(c.ops[0], ast::CmpOp::Gt | ast::CmpOp::GtE) {
                    E::name(name).app(right).app(left)
                } else {
                    E::name(name).app(left).app(right)
                };
                let term = if c.ops[0] == ast::CmpOp::NotEq {
                    E::name("deppy.verified.bool_not").app(term)
                } else {
                    term
                };
                (term, Scalar::Bool)
            }
            Expr::BoolOp(op) => {
                let (last, earlier) = op
                    .values
                    .split_last()
                    .ok_or_else(|| error(op, "empty boolean operation"))?;
                let mut value = self.value(last, state, Some(Scalar::Bool))?.0;
                for operand in earlier.iter().rev() {
                    let test = self.value(operand, state, Some(Scalar::Bool))?.0;
                    let (no, yes) = if op.op == ast::BoolOp::And {
                        (E::name("deppy.data.False_"), value)
                    } else {
                        (value, E::name("deppy.data.True_"))
                    };
                    value = E::name("deppy.verified.select")
                        .implicit(Scalar::Bool.expr())
                        .app(test)
                        .app(no)
                        .app(yes);
                }
                (value, Scalar::Bool)
            }
            Expr::If(op) => {
                let test = self.value(&op.test, state, Some(Scalar::Bool))?.0;
                let (yes, ty) = self.value(&op.body, state, expected)?;
                let no = self.value(&op.orelse, state, Some(ty))?.0;
                (
                    E::name("deppy.verified.select")
                        .implicit(ty.expr())
                        .app(test)
                        .app(no)
                        .app(yes),
                    ty,
                )
            }
            Expr::UnaryOp(op) if op.op == ast::UnaryOp::USub => {
                let value = self.value(&op.operand, state, Some(Scalar::Int))?.0;
                (E::name("deppy.integer.neg").app(value), Scalar::Int)
            }
            Expr::UnaryOp(op) if op.op == ast::UnaryOp::Not => {
                let value = self.value(&op.operand, state, Some(Scalar::Bool))?.0;
                (E::name("deppy.verified.bool_not").app(value), Scalar::Bool)
            }
            Expr::Call(c) => {
                // Calls are only to already checked pure definitions, never host
                // functions, locals, recursive self calls or Python attributes.
                let Expr::Name(n) = c.func.as_ref() else {
                    return Err(error(c, "verified calls require a checked function name"));
                };
                if n.id.as_str() == "$int_literal" {
                    if expected.is_some_and(|t| t != Scalar::Int) {
                        return Err(error(c, "verified scalar type mismatch"));
                    }
                    let value = self
                        .value(&c.arguments.args[0], state, Some(Scalar::Nat))?
                        .0;
                    return Ok((
                        E::name("deppy.integer.Pos")
                            .app(value)
                            .ann(Scalar::Int.expr()),
                        Scalar::Int,
                    ));
                }
                if n.id.as_str().starts_with("$arith_") {
                    return self.numeric_call(c, state, expected);
                }
                if let Some(helper) = range::helper(n.id.as_str()) {
                    if state.scope.locals.contains("range")
                        || state.scope.assigned.contains("range")
                        || self.globals.contains_key("range")
                    {
                        return Err(error(c, "for range requires the unshadowed range builtin"));
                    }
                    let mut term = E::name(helper);
                    for argument in &c.arguments.args {
                        term = term.app(self.value(argument, state, None)?.0);
                    }
                    return Ok((term.ann(E::Nat), Scalar::Nat));
                }
                if state.scope.locals.contains(n.id.as_str())
                    || state.scope.assigned.contains(n.id.as_str())
                {
                    return Err(error(c, "verified local values are not callable"));
                }
                if !self.globals.contains_key(n.id.as_str())
                    && self.builtin(&c.func, &state.scope) != Some("S")
                {
                    return Err(error(c, "verified calls require a checked pure function"));
                }
                if !state.allow_contracts
                    && self.globals.get(n.id.as_str()).is_some_and(|b| b.verified)
                {
                    return Err(error(
                        c,
                        "contract calls require automatic or named verification; while guards do not support contract calls",
                    ));
                }
                if !c.arguments.keywords.is_empty() {
                    return Err(error(c, "verified pure calls require positional arguments"));
                }
                let mut term = self.expr(&c.func, &state.scope)?;
                for argument in &c.arguments.args {
                    term = term.app(self.value(argument, state, None)?.0);
                }
                let contract_result = self
                    .globals
                    .get(n.id.as_str())
                    .and_then(|binding| binding.contract.as_ref())
                    .map(|contract| contract.result);
                (
                    term,
                    expected
                        .or(contract_result)
                        .or_else(|| self.numeric_hint(e, state))
                        .unwrap_or(Scalar::Nat),
                )
            }
            _ => return Err(error(e, "unsupported verified value expression")),
        };
        if expected.is_some_and(|expected| expected != ty) {
            return Err(error(e, "verified scalar type mismatch"));
        }
        // In particular, check the declared result type of every pure call.
        Ok((term.ann(ty.expr()), ty))
    }
}
