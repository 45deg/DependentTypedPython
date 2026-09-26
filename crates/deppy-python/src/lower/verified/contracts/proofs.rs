//! Named VC proofs and refinement evidence.
use super::super::*;

pub(in crate::lower::verified) struct Proofs<'a> {
    entries: HashMap<String, &'a Expr>,
    used: HashSet<String>,
    counts: HashMap<String, usize>,
    function: String,
    automatic: bool,
    pub(in crate::lower::verified) denotation_only: bool,
    pub(in crate::lower::verified) hints: Vec<String>,
}
impl<'a> Proofs<'a> {
    pub(in crate::lower::verified) fn empty(function: &str, automatic: bool) -> Self {
        Self {
            entries: HashMap::new(),
            used: HashSet::new(),
            counts: HashMap::new(),
            function: function.into(),
            automatic,
            denotation_only: false,
            hints: vec![],
        }
    }

    pub(in crate::lower::verified) fn parse(
        expr: &'a Expr,
        function: &str,
        automatic: bool,
    ) -> Result<Self, Diagnostic> {
        let Expr::Dict(dict) = expr else {
            return Err(error(
                expr,
                "proofs requires a dictionary of named VC proofs",
            ));
        };
        let mut entries = HashMap::new();
        for item in &dict.items {
            let Some(Expr::StringLiteral(key)) = &item.key else {
                return Err(error(expr, "proofs keys must be literal strings"));
            };
            if entries
                .insert(key.value.to_str().to_owned(), &item.value)
                .is_some()
            {
                return Err(error(key, "duplicate VC proof name"));
            }
        }
        Ok(Self {
            entries,
            used: HashSet::new(),
            counts: HashMap::new(),
            function: function.into(),
            automatic,
            denotation_only: false,
            hints: vec![],
        })
    }
    pub(in crate::lower::verified) fn automatic_only(&self) -> bool {
        self.automatic && self.entries.is_empty()
    }
    pub(in crate::lower::verified) fn finish(&self) -> Result<(), Diagnostic> {
        if let Some((key, expr)) = self
            .entries
            .iter()
            .filter(|(k, _)| !self.used.contains(*k))
            .min_by_key(|(k, _)| *k)
        {
            return Err(error(*expr, format!("unknown or unused VC proof: {key}")));
        }
        Ok(())
    }
    pub(in crate::lower::verified) fn call_key(&mut self, path: &str, name: &str) -> String {
        self.assignment_key(path, "call", name, "requires")
    }
    pub(in crate::lower::verified) fn assertion_key(
        &mut self,
        path: &str,
        source: &Expr,
    ) -> String {
        if let Expr::Call(c) = source {
            if let Expr::Name(n) = c.func.as_ref() {
                if let Some(operation) = n.id.as_str().strip_prefix("$arith_safe_") {
                    return self.assignment_key(path, "arithmetic", operation, "safe");
                }
            }
        }
        if matches!(source, Expr::Compare(c) if matches!(c.comparators.first(), Some(Expr::Name(n)) if n.id.as_str().starts_with("$expr_range_stride")))
        {
            self.assignment_key(path, "range", "step", "positive")
        } else {
            self.assignment_key(path, "assert", "test", "holds")
        }
    }
    pub(in crate::lower::verified) fn assignment_key(
        &mut self,
        path: &str,
        kind: &str,
        name: &str,
        suffix: &str,
    ) -> String {
        let base = format!("{path}{kind}.{name}");
        let count = self.counts.entry(base.clone()).or_default();
        *count += 1;
        if *count == 1 {
            format!("{base}.{suffix}")
        } else {
            format!("{base}.{}.{suffix}", *count)
        }
    }
}

impl Lowerer {
    pub(in crate::lower::verified) fn obligation(
        &mut self,
        proofs: &mut Proofs<'_>,
        key: &str,
        source: &Expr,
        context: &[(String, E)],
        goal: E,
    ) -> Result<E, Diagnostic> {
        proofs.used.insert(key.into());
        let proof = if let Some(expr) = proofs.entries.get(key) {
            if let Expr::Lambda(lambda) = expr {
                let parameters = lambda
                    .parameters
                    .as_deref()
                    .ok_or_else(|| error(lambda, "VC proof lambda requires context parameters"))?;
                self.parameters(parameters)?;
                let parameters = parameters
                    .posonlyargs
                    .iter()
                    .chain(&parameters.args)
                    .collect::<Vec<_>>();
                if parameters.len() != context.len() {
                    return Err(error(
                        lambda,
                        format!(
                            "VC {key} proof requires {} context parameters",
                            context.len()
                        ),
                    ));
                }
                // Instantiate the proof callback in the actual symbolic context.
                // Re-abstracting entry variables here would detach their SSA lets
                // from those variables, especially in loop initialization goals.
                let mut scope = Scope::default();
                for (parameter, (name, _)) in parameters.iter().zip(context) {
                    let local = parameter.parameter.name.to_string();
                    scope.locals.insert(local.clone());
                    scope.aliases.insert(local, name.clone());
                }
                self.expr(&lambda.body, &scope)?
            } else {
                let mut proof = self.expr(expr, &Scope::default())?;
                for (name, _) in context {
                    proof = proof.app(E::name(name));
                }
                proof
            }
        } else {
            let name = format!("{}.{}", proofs.function, key);
            let goal = if proofs.automatic {
                E::AutoProof {
                    name,
                    hints: [
                        "deppy.data.MkUnit",
                        "deppy.arithmetic.sub_bound",
                        "deppy.arithmetic.divisor_positive",
                        "deppy.arithmetic.nonzero_positive",
                        "deppy.arithmetic.unequal_zero_positive",
                        "deppy.arithmetic.remainder_lt_true",
                        "deppy.verified.false_true_elim",
                        "deppy.verified.true_false_elim",
                        "deppy.verified.nat_lt_not_false",
                        "deppy.verified.nat_eq_true",
                        "deppy.integer.eq_true",
                        "deppy.verified.nat_le_refl_true",
                        "deppy.verified_loop.range_bound",
                        "deppy.verified_loop.range_decrease",
                        "deppy.verified_loop.positive_stride",
                        "deppy.nat_order.le_refl",
                        "deppy.verified.nat_lt_true",
                        "deppy.verified.nat_le_true",
                        "deppy.verified.nat_lt_false_zero",
                        "deppy.nat_order.pred_lt",
                        "deppy.verified.pred_lt_true",
                        "deppy.verified.lt_le_bound",
                        "deppy.nat_order.le_weaken",
                        "deppy.nat_order.le_trans",
                    ]
                    .into_iter()
                    .map(str::to_owned)
                    .chain(proofs.hints.iter().cloned())
                    .collect(),
                }
            } else {
                E::UserHole(name)
            };
            goal.located(deppy_elab::SourceLocation {
                source: self.namespace.clone(),
                start: source.range().start().to_usize(),
                end: source.range().end().to_usize(),
            })
        };
        Ok(proof.ann(goal))
    }

    pub(in crate::lower::verified) fn local_condition(
        &mut self,
        name: &str,
        scalar: Scalar,
        predicate: &Expr,
        state: &mut State,
    ) -> Result<(), Diagnostic> {
        if state.refinements.contains_key(name) {
            return Err(error(
                predicate,
                "a local refinement may only be declared once",
            ));
        }
        if state.types.get(name).is_some_and(|old| *old != scalar) {
            return Err(error(
                predicate,
                "verified reassignment cannot change a local's type",
            ));
        }
        let condition = self.expr(predicate, &state.scope)?.ann(E::pi(
            "$value",
            Plicity::Explicit,
            scalar.expr(),
            E::Universe(0),
        ));
        state.refinements.insert(name.into(), condition);
        Ok(())
    }

    pub(in crate::lower::verified) fn local_evidence(
        &mut self,
        names: &[(&str, &Expr)],
        state: &State,
        context: &mut Vec<(String, E)>,
        path: &str,
        proofs: &mut Proofs<'_>,
    ) -> Result<Vec<(String, E, E)>, Diagnostic> {
        let mut bindings = vec![];
        for (name, source) in names {
            if let Some(predicate) = state.refinements.get(*name) {
                let value_name = state.scope.aliases.get(*name).unwrap();
                if !context.iter().any(|(n, _)| n == value_name) {
                    context.push((value_name.clone(), state.types[*name].expr()));
                }
                let goal = predicate.clone().app(E::name(value_name));
                let key = proofs.assignment_key(path, "local", name, "refined");
                let proof = self.obligation(proofs, &key, source, context, goal.clone())?;
                let fact = format!("$local_fact{}", self.wildcard);
                self.wildcard += 1;
                context.push((fact.clone(), goal.clone()));
                bindings.push((fact, goal, proof));
            }
        }
        Ok(bindings)
    }
}
