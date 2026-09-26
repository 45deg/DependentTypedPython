use super::*;
mod check;
mod nat;
mod synth;

impl State {
    fn type_error(&self, ctx: &Context, error: Error, expected: &str, actual: &T) -> Error {
        if self.location.is_none() {
            return error;
        }
        Error::WithTypes {
            expected: expected.into(),
            actual: self.describe(actual, ctx),
            error: Box::new(error),
        }
    }
    fn unify_types(&mut self, ctx: &Context, actual: &T, expected: &T) -> Result<(), Error> {
        self.unify(actual, expected).map_err(|error| {
            if self.location.is_some() && matches!(error, Error::CannotUnify) {
                Error::TypeMismatch {
                    expected: self.describe(expected, ctx),
                    actual: self.describe(actual, ctx),
                }
            } else {
                error
            }
        })
    }

    pub(crate) fn type_expr(&mut self, ctx: &Context, expr: &Expr) -> Result<(T, u32), Error> {
        if let Expr::Located {
            location,
            expression,
        } = expr
        {
            let previous = self.location.replace(location.clone());
            let result = self
                .type_expr(ctx, expression)
                .map_err(|error| error.at(location));
            self.location = previous;
            return result;
        }
        let (term, ty) = self.synth(ctx, expr)?;
        match self.whnf(&ty)?.as_ref() {
            Term::Universe(level) => Ok((term, *level)),
            _ => Err(self.type_error(ctx, Error::ExpectedUniverse, "a universe", &ty)),
        }
    }

    // Preserve a transparent reference at lookup. Conversion can unfold it,
    // while core lowering emits a real let and retains even unused definitions
    // for independent kernel checking.
    fn let_expr(
        &mut self,
        ctx: &Context,
        name: &str,
        annotation: Option<&Expr>,
        value: &Expr,
        body: &Expr,
        expected: Option<&T>,
    ) -> Result<(T, T), Error> {
        let (value, ty) = if let Some(annotation) = annotation {
            let (ty, _) = self.type_expr(ctx, annotation)?;
            (self.check(ctx, value, &ty)?, ty)
        } else {
            self.synth(ctx, value)?
        };
        let (mut inner, id) = self.bind(ctx, name, ty.clone());
        inner.last_mut().unwrap().value = Some(
            Term::Defined {
                id,
                value: value.clone(),
            }
            .arc(),
        );
        let (body, result) = if let Some(expected) = expected {
            (self.check(&inner, body, expected)?, expected.clone())
        } else {
            self.synth(&inner, body)?
        };
        Ok((
            Term::App(
                Term::Lam {
                    id,
                    plicity: Plicity::Explicit,
                    domain: ty,
                    body,
                }
                .arc(),
                value,
            )
            .arc(),
            result,
        ))
    }
}
