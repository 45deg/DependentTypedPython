use super::*;
use deppy_elab::lower::{Arm, Body, Pattern};

#[derive(Clone)]
enum Cell {
    Capture(Option<String>),
    Constructor {
        name: String,
        family: String,
        fields: Vec<Cell>,
        constructors: Vec<(String, usize)>,
        location: deppy_elab::SourceLocation,
    },
}
#[derive(Clone)]
struct Row<'a> {
    cells: Vec<Cell>,
    body: &'a [Stmt],
    scope: Scope,
    index: usize,
}
impl Lowerer {
    pub(super) fn general_matrix(&self, statement: &ast::StmtMatch, scope: &Scope) -> bool {
        statement.cases.iter().all(|case| matches!(&case.pattern, ast::Pattern::MatchAs(capture) if capture.pattern.is_none())) || statement.cases.iter().any(|case| match &case.pattern {
            ast::Pattern::MatchClass(class) => match class.cls.as_ref() {
                Expr::Name(name) if !scope.locals.contains(name.id.as_str()) => self
                    .globals
                    .get(name.id.as_str())
                    .is_some_and(|b| b.data.is_some()),
                _ => false,
            },
            _ => false,
        })
    }
    fn cell(&mut self, pattern: &ast::Pattern, scope: &mut Scope) -> Result<Cell, Diagnostic> {
        self.tick(pattern.range())?;
        match pattern {
            ast::Pattern::MatchAs(capture) if capture.pattern.is_none() => {
                if let Some(name) = &capture.name {
                    self.bind(scope, name.as_str(), name)?;
                }
                Ok(Cell::Capture(
                    capture.name.as_ref().map(ToString::to_string),
                ))
            }
            ast::Pattern::MatchClass(class) => {
                let Expr::Name(name) = class.cls.as_ref() else {
                    return Err(error(pattern, "expected a named constructor"));
                };
                let binding = self
                    .globals
                    .get(name.id.as_str())
                    .cloned()
                    .ok_or_else(|| error(pattern, "unknown constructor"))?;
                let data = binding
                    .data
                    .ok_or_else(|| error(pattern, "expected an inductive constructor"))?;
                let c = data
                    .constructor
                    .ok_or_else(|| error(pattern, "expected a constructor, not a family"))?;
                if !class.arguments.keywords.is_empty()
                    || class.arguments.patterns.len() != data.constructors[c].1
                {
                    return Err(error(pattern, "wrong constructor arity or keyword pattern"));
                }
                let fields = class
                    .arguments
                    .patterns
                    .iter()
                    .map(|p| self.cell(p, scope))
                    .collect::<Result<_, _>>()?;
                Ok(Cell::Constructor {
                    name: binding.name,
                    family: data.family,
                    constructors: data.constructors,
                    fields,
                    location: deppy_elab::SourceLocation {
                        source: self.namespace.clone(),
                        start: pattern.range().start().to_usize(),
                        end: pattern.range().end().to_usize(),
                    },
                })
            }
            _ => Err(error(
                pattern,
                "expected a constructor, capture, or wildcard pattern",
            )),
        }
    }
    pub(super) fn matrix(
        &mut self,
        statement: &ast::StmtMatch,
        scope: &Scope,
    ) -> Result<Body, Diagnostic> {
        let Expr::Name(subject) = statement.subject.as_ref() else {
            return Err(error(statement, "match subject must be a local name"));
        };
        let subject = scope
            .aliases
            .get(subject.id.as_str())
            .cloned()
            .unwrap_or_else(|| subject.id.to_string());
        let mut rows = vec![];
        for (index, case) in statement.cases.iter().enumerate() {
            if case.guard.is_some() {
                return Err(error(case, "match guards are unsupported"));
            }
            let mut inner = scope.clone();
            let cell = self.cell(&case.pattern, &mut inner)?;
            rows.push(Row {
                cells: vec![cell],
                body: &case.body,
                scope: inner,
                index,
            });
        }
        let mut used = HashSet::new();
        let result = self.split_matrix(vec![subject], rows, &mut used)?;
        for (index, case) in statement.cases.iter().enumerate() {
            if !used.contains(&index) {
                return Err(error(
                    &case.pattern,
                    "duplicate or unreachable constructor branch",
                ));
            }
        }
        Ok(result.located(deppy_elab::SourceLocation {
            source: self.namespace.clone(),
            start: statement.range().start().to_usize(),
            end: statement.range().end().to_usize(),
        }))
    }
    fn split_matrix(
        &mut self,
        subjects: Vec<String>,
        rows: Vec<Row<'_>>,
        used: &mut HashSet<usize>,
    ) -> Result<Body, Diagnostic> {
        let first = &rows[0];
        let Some(column) = first
            .cells
            .iter()
            .position(|cell| matches!(cell, Cell::Constructor { .. }))
        else {
            let mut scope = first.scope.clone();
            for (cell, subject) in first.cells.iter().zip(&subjects) {
                if let Cell::Capture(Some(name)) = cell {
                    scope.aliases.insert(name.clone(), subject.clone());
                }
            }
            used.insert(first.index);
            return self.structural_body(first.body, &scope);
        };
        let Cell::Constructor {
            family,
            constructors,
            location,
            ..
        } = &first.cells[column]
        else {
            unreachable!()
        };
        self.tick(TextRange::new(
            (location.start as u32).into(),
            (location.end as u32).into(),
        ))?;
        for row in &rows {
            if let Cell::Constructor {
                family: other,
                location,
                ..
            } = &row.cells[column]
            {
                if other != family {
                    return Err(Diagnostic {
                        details: Default::default(),
                        span: crate::Span {
                            start: location.start,
                            end: location.end,
                        },
                        message: "constructors belong to different families".into(),
                    });
                }
            }
        }
        let mut arms = vec![];
        for (name, arity) in constructors {
            let branch_location = rows
                .iter()
                .find_map(|row| match &row.cells[column] {
                    Cell::Constructor {
                        name: other,
                        location,
                        ..
                    } if other == name => Some(location.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| location.clone());
            let fields = (0..*arity)
                .map(|_| {
                    let n = format!("$pattern{}", self.wildcard);
                    self.wildcard += 1;
                    n
                })
                .collect::<Vec<_>>();
            let mut specialized = vec![];
            for row in &rows {
                let mut row = row.clone();
                let cell = row.cells.remove(column);
                let children = match cell {
                    Cell::Constructor {
                        name: other,
                        fields,
                        ..
                    } if other == *name => fields,
                    Cell::Constructor { .. } => continue,
                    Cell::Capture(capture) => {
                        if let Some(capture) = capture {
                            row.scope.aliases.insert(capture, subjects[column].clone());
                        }
                        vec![Cell::Capture(None); *arity]
                    }
                };
                row.cells.splice(column..column, children);
                specialized.push(row);
            }
            if specialized.is_empty() {
                continue;
            }
            let mut next = subjects.clone();
            next.splice(column..=column, fields.clone());
            let body = self.split_matrix(next, specialized, used)?;
            arms.push(Arm {
                pattern: Pattern::Constructor {
                    name: name.clone(),
                    fields,
                }
                .located(branch_location),
                body,
            });
        }
        Ok(Body::Match {
            scrutinee: subjects[column].clone(),
            arms,
        }
        .located(location.clone()))
    }
}
