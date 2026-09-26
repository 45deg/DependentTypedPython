//! Nat ranges use an immutable cursor and a structurally computed iteration count.
//! Generated names cannot be written by source programs. Continue advances both
//! fields before the body, while break and return use ordinary control outcomes.
use super::*;
use normalize::assign;

pub(super) fn helper(name: &str) -> Option<&'static str> {
    match name {
        "$range_count" => Some("deppy.verified_loop.range_count"),
        "$range_next" => Some("deppy.verified_loop.range_next"),
        "$range_pred" => Some("deppy.nat.pred_or"),
        _ => None,
    }
}
fn name(id: &str, source: &Expr) -> Expr {
    Expr::Name(ast::ExprName {
        range: source.range(),
        id: id.into(),
        ctx: ast::ExprContext::Load,
        node_index: Default::default(),
    })
}
fn number(value: u32, source: &Expr) -> Expr {
    Expr::NumberLiteral(ast::ExprNumberLiteral {
        range: source.range(),
        value: ast::Number::Int(value.into()),
        node_index: Default::default(),
    })
}
fn call(function: &str, args: Vec<Expr>, source: &Expr) -> Expr {
    Expr::Call(ast::ExprCall {
        range_start: source.range().start(),
        func: Box::new(name(function, source)),
        arguments: ast::Arguments {
            range: source.range(),
            args: args.into_boxed_slice(),
            keywords: Default::default(),
            node_index: Default::default(),
        },
        node_index: Default::default(),
    })
}
fn positive(value: Expr, source: &Expr) -> Expr {
    Expr::Compare(ast::ExprCompare {
        range: source.range(),
        left: Box::new(number(0, source)),
        ops: vec![ast::CmpOp::Lt].into_boxed_slice(),
        comparators: vec![value].into_boxed_slice(),
        node_index: Default::default(),
    })
}
impl Lowerer {
    pub(super) fn normalize_range(&mut self, f: &ast::StmtFor) -> Result<Vec<Stmt>, Diagnostic> {
        let Expr::Call(iter) = f.iter.as_ref() else {
            return Err(error(f, "verified for requires range(...)"));
        };
        if f.is_async
            || !f.orelse.is_empty()
            || !matches!(f.target.as_ref(), Expr::Name(_))
            || !matches!(iter.func.as_ref(), Expr::Name(n) if n.id.as_str() == "range")
            || !iter.arguments.keywords.is_empty()
            || !(1..=3).contains(&iter.arguments.args.len())
        {
            return Err(error(f, "use for local in range(stop), range(start, stop), or range(start, stop, step); for-else is unsupported"));
        }
        let source = f.iter.as_ref();
        let args = &iter.arguments.args;
        let start = if args.len() == 1 {
            number(0, source)
        } else {
            args[0].clone()
        };
        let stop = args[usize::from(args.len() > 1)].clone();
        let mut stride = args.get(2).cloned().unwrap_or_else(|| number(1, source));
        let descending = if let Expr::UnaryOp(op) = &stride {
            if op.op != ast::UnaryOp::USub
                || !matches!(op.operand.as_ref(), Expr::NumberLiteral(n) if matches!(n.value, ast::Number::Int(_)))
            {
                return Err(error(
                    &stride,
                    "descending range requires a negative integer literal step",
                ));
            }
            stride = *op.operand.clone();
            true
        } else {
            false
        };
        let direction = Expr::BooleanLiteral(ast::ExprBooleanLiteral {
            range: source.range(),
            value: descending,
            node_index: Default::default(),
        });
        let id = self.wildcard;
        self.wildcard += 1;
        let cursor = name(&format!("$expr_range_cursor{id}"), source);
        let bound = name(&format!("$expr_range_stop{id}"), source);
        let step = name(&format!("$expr_range_stride{id}"), source);
        let remaining = name(&format!("$expr_range_remaining{id}"), source);
        let mut output = vec![];
        for (target, expression) in [
            (cursor.clone(), start),
            (bound.clone(), stop),
            (step.clone(), stride.clone()),
        ] {
            let value = self.normalize_value(&expression, &mut output, true)?;
            output.push(assign(target, value));
        }
        output.push(Stmt::Assert(ast::StmtAssert {
            range: stride.range(),
            test: Box::new(positive(step.clone(), &stride)),
            msg: None,
            node_index: Default::default(),
        }));
        output.push(assign(
            remaining.clone(),
            call(
                "$range_count",
                vec![
                    cursor.clone(),
                    bound.clone(),
                    step.clone(),
                    direction.clone(),
                ],
                source,
            ),
        ));
        // Definite initialization is required so an empty range preserves the
        // target's entry value instead of inventing a value for an unbound name.
        output.push(assign(*f.target.clone(), *f.target.clone()));
        let mut body = self.normalize_commands(&f.body)?;
        let mut header = vec![];
        if matches!(body.first(), Some(Stmt::Expr(e)) if matches!(e.value.as_ref(), Expr::Call(c) if self.builtin(&c.func, &Scope::default()) == Some("invariant")))
        {
            header.push(body.remove(0));
        }
        header.push(Stmt::Expr(ast::StmtExpr {
            range: source.range(),
            value: Box::new(call("$range_decreases", vec![remaining.clone()], source)),
            node_index: Default::default(),
        }));
        header.push(assign(*f.target.clone(), cursor.clone()));
        header.push(assign(
            cursor.clone(),
            call("$range_next", vec![cursor.clone(), step, direction], source),
        ));
        header.push(assign(
            remaining.clone(),
            call(
                "$range_pred",
                vec![number(0, source), remaining.clone()],
                source,
            ),
        ));
        header.extend(body);
        header.push(Stmt::Continue(ast::StmtContinue {
            range: f.range,
            node_index: Default::default(),
        }));
        let bound_test = Expr::Compare(ast::ExprCompare {
            node_index: Default::default(),
            range: source.range(),
            left: Box::new(if descending {
                bound.clone()
            } else {
                cursor.clone()
            }),
            ops: vec![ast::CmpOp::Lt].into_boxed_slice(),
            comparators: vec![if descending { cursor } else { bound }].into_boxed_slice(),
        });
        let guard = Expr::BoolOp(ast::ExprBoolOp {
            node_index: Default::default(),
            range: source.range(),
            op: ast::BoolOp::And,
            values: vec![positive(remaining, source), bound_test],
        });
        output.push(Stmt::While(ast::StmtWhile {
            range: f.range,
            test: Box::new(guard),
            body: header.into_iter().collect(),
            orelse: Default::default(),
            node_index: Default::default(),
        }));
        Ok(output)
    }
}
