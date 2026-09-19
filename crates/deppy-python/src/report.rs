//! Machine-readable analysis output without a serialization dependency.
use crate::{Analysis, Diagnostic};

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
            "{{\"checked\":{},\"diagnostics\":[{}],\"goals\":[{}]}}",
            self.checked.is_some(),
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
