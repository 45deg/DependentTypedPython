//! Machine-readable analysis output without a serialization dependency.
use crate::{Analysis, Diagnostic};
use std::fmt::{self, Write};

struct LimitedDebug {
    output: String,
    limit: usize,
}

impl Write for LimitedDebug {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let remaining = self.limit.saturating_sub(self.output.len());
        if value.len() <= remaining {
            self.output.push_str(value);
            return Ok(());
        }
        let mut end = remaining;
        while !value.is_char_boundary(end) {
            end -= 1;
        }
        self.output.push_str(&value[..end]);
        Err(fmt::Error)
    }
}

fn core_debug(value: &impl fmt::Debug) -> String {
    let mut writer = LimitedDebug {
        output: String::new(),
        limit: 12_000,
    };
    if write!(writer, "{value:#?}").is_err() {
        writer.output.push_str("\n… truncated");
    }
    writer.output
}

fn string(value: &str) -> String {
    let mut result = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c <= '\u{1f}' => result.push_str(&format!("\\u{:04x}", c as u32)),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}
fn optional(value: Option<&str>) -> String {
    value.map(string).unwrap_or_else(|| "null".into())
}
fn number(value: Option<usize>) -> String {
    value
        .map(|n| n.to_string())
        .unwrap_or_else(|| "null".into())
}
fn diagnostic(error: &Diagnostic) -> String {
    let related = error
        .details
        .related
        .iter()
        .map(|location| {
            format!(
                "{{\"source\":{},\"start\":{},\"end\":{}}}",
                string(&location.source),
                location.start,
                location.end
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{{\"kind\":{},\"message\":{},\"source\":{},\"start\":{},\"end\":{},\"line\":{},\"column\":{},\"expected\":{},\"actual\":{},\"related\":[{}]}}",
        string(&format!("{:?}", error.details.kind)), string(&error.message), optional(error.details.source.as_deref()),
        error.span.start, error.span.end, number(error.details.line), number(error.details.column),
        optional(error.details.expected.as_deref()), optional(error.details.actual.as_deref()), related)
}
impl Analysis {
    /// Stable JSON object containing checked status, diagnostics, and open goals.
    pub fn to_json(&self) -> String {
        let declarations = self.checked.as_ref().map_or_else(String::new, |checked| {
            checked
                .definitions
                .iter()
                .filter_map(|(name, id, span)| {
                    let entry = checked.interface.exports().get(name)?;
                    let declaration = checked.interface.kernel().definition(*id).ok()?;
                    let proof = declaration.body.as_ref().map(core_debug);
                    let verified_spec = entry
                        .verified_spec
                        .and_then(|id| checked.interface.kernel().definition(id).ok())
                        .map(|theorem| {
                            format!(
                                "{{\"type\":{},\"term\":{}}}",
                                string(&core_debug(&theorem.ty)),
                                optional(theorem.body.as_ref().map(core_debug).as_deref()),
                            )
                        })
                        .unwrap_or_else(|| "null".into());
                    let axioms = entry
                        .axiom_dependencies
                        .iter()
                        .map(|name| string(name))
                        .collect::<Vec<_>>()
                        .join(",");
                    Some(format!(
                        "{{\"name\":{},\"kind\":{},\"start\":{},\"end\":{},\"type\":{},\"term\":{},\"verifiedSpec\":{},\"axioms\":[{}]}}",
                        string(name),
                        string(&format!("{:?}", entry.kind)),
                        span.start,
                        span.end,
                        string(&core_debug(&entry.ty)),
                        optional(proof.as_deref()),
                        verified_spec,
                        axioms,
                    ))
                })
                .collect::<Vec<_>>()
                .join(",")
        });
        let goals = self
            .goals
            .iter()
            .map(|goal| {
                let location = goal
                    .location
                    .as_ref()
                    .map(|loc| {
                        format!(
                            "{{\"source\":{},\"start\":{},\"end\":{}}}",
                            string(&loc.source),
                            loc.start,
                            loc.end
                        )
                    })
                    .unwrap_or_else(|| "null".into());
                let context = goal
                    .context
                    .iter()
                    .map(|local| {
                        format!(
                            "{{\"name\":{},\"type\":{},\"value\":{}}}",
                            string(&local.name),
                            string(&local.ty),
                            optional(local.value.as_deref())
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!(
                    "{{\"id\":{},\"name\":{},\"location\":{},\"context\":[{}],\"expected\":{}}}",
                    goal.id,
                    string(&goal.name),
                    location,
                    context,
                    string(&goal.expected)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"checked\":{},\"declarations\":[{}],\"diagnostics\":[{}],\"goals\":[{}]}}",
            self.checked.is_some(),
            declarations,
            self.diagnostics
                .iter()
                .map(diagnostic)
                .collect::<Vec<_>>()
                .join(","),
            goals
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn json_strings_escape_quotes_backslashes_controls_and_preserve_unicode() {
        assert_eq!(
            super::string("証明\"\\\n\r\t\0\u{1f}"),
            "\"証明\\\"\\\\\\n\\r\\t\\u0000\\u001f\""
        );
    }
}
