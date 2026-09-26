//! Checked numeric operations are introduced only by expression normalization.
use super::*;
impl Lowerer {
    pub(super) fn numeric_hint(&self, expression: &Expr, state: &State) -> Option<Scalar> {
        match expression {
            Expr::Name(n) => state.types.get(n.id.as_str()).copied(),
            Expr::BooleanLiteral(_) | Expr::BoolOp(_) | Expr::Compare(_) => Some(Scalar::Bool),
            Expr::UnaryOp(u) if u.op == ast::UnaryOp::Not => Some(Scalar::Bool),
            Expr::UnaryOp(u) if u.op == ast::UnaryOp::USub => Some(Scalar::Int),
            Expr::If(i) => self
                .numeric_hint(&i.body, state)
                .or_else(|| self.numeric_hint(&i.orelse, state)),
            Expr::BinOp(b) => self
                .numeric_hint(&b.left, state)
                .or_else(|| self.numeric_hint(&b.right, state)),
            Expr::Call(c) => {
                let Expr::Name(n) = c.func.as_ref() else {
                    return None;
                };
                if n.id.as_str() == "$int_literal" {
                    return Some(Scalar::Int);
                }
                if n.id.as_str().starts_with("$arith_") {
                    return Some(self.numeric_type(
                        &c.arguments.args[0],
                        &c.arguments.args[1],
                        state,
                        None,
                    ));
                }
                let binding = self.globals.get(n.id.as_str())?;
                if let Some(contract) = &binding.contract {
                    return Some(contract.result);
                }
                match binding.name.as_str() {
                    "deppy.integer.Pos"
                    | "deppy.integer.Neg"
                    | "deppy.integer.of_nat"
                    | "deppy.integer.negative_nat"
                    | "deppy.integer.neg"
                    | "deppy.integer.pred"
                    | "deppy.integer.add"
                    | "deppy.integer.sub"
                    | "deppy.integer.mul"
                    | "deppy.integer.quotient"
                    | "deppy.integer.remainder" => Some(Scalar::Int),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    pub(super) fn numeric_type(
        &self,
        left: &Expr,
        right: &Expr,
        state: &State,
        expected: Option<Scalar>,
    ) -> Scalar {
        if expected == Some(Scalar::Int)
            || self.numeric_hint(left, state) == Some(Scalar::Int)
            || self.numeric_hint(right, state) == Some(Scalar::Int)
        {
            Scalar::Int
        } else {
            Scalar::Nat
        }
    }
    pub(super) fn numeric_call(
        &mut self,
        c: &ast::ExprCall,
        state: &State,
        expected: Option<Scalar>,
    ) -> Result<(E, Scalar), Diagnostic> {
        let Expr::Name(name) = c.func.as_ref() else {
            unreachable!()
        };
        let operation = name.id.as_str().strip_prefix("$arith_").unwrap();
        let safe = operation.starts_with("safe_");
        let operation = operation.strip_prefix("safe_").unwrap_or(operation);
        let ty = self.numeric_type(
            &c.arguments.args[0],
            &c.arguments.args[1],
            state,
            if safe { None } else { expected },
        );
        let left = self.value(&c.arguments.args[0], state, Some(ty))?.0;
        let right = self.value(&c.arguments.args[1], state, Some(ty))?.0;
        let (value, ty) = if safe {
            let condition = match (operation, ty) {
                ("sub", Scalar::Int) => E::name("deppy.data.True_"),
                ("sub", _) => E::name("deppy.verified.nat_le").app(right).app(left),
                (_, Scalar::Int) => E::name("deppy.verified.bool_not").app(
                    E::name("deppy.integer.eq")
                        .app(right)
                        .app(E::name("deppy.integer.Pos").app(E::Zero)),
                ),
                _ => E::name("deppy.verified.nat_lt").app(E::Zero).app(right),
            };
            (condition, Scalar::Bool)
        } else {
            let name = match operation {
                "sub" => "sub",
                "div" => "quotient",
                "mod" => "remainder",
                _ => unreachable!(),
            };
            let module = if ty == Scalar::Int {
                "integer"
            } else {
                "arithmetic"
            };
            (
                E::name(format!("deppy.{module}.{name}"))
                    .app(left)
                    .app(right),
                ty,
            )
        };
        if expected.is_some_and(|e| e != ty) {
            return Err(error(c, "verified scalar type mismatch"));
        }
        Ok((value.ann(ty.expr()), ty))
    }
}
