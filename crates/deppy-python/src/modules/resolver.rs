/// Return source for a checked module name. None means the module is unavailable.
/// The resolver supplies data, never executed Python objects.
pub trait SourceResolver {
    fn source(&mut self, name: &str) -> Result<Option<String>, String>;
    /// Display identity of a previously resolved source; never used for name resolution.
    fn source_name(&self, name: &str) -> String {
        name.into()
    }
}
impl<F: FnMut(&str) -> Result<Option<String>, String>> SourceResolver for F {
    fn source(&mut self, name: &str) -> Result<Option<String>, String> {
        self(name)
    }
}
/// Resolve .py files (or package __init__.py files) under a fixed source root.
/// Canonical paths must stay inside that root, including through symlinks.
pub struct FileResolver {
    root: std::path::PathBuf,
    paths: std::collections::HashMap<String, String>,
}
impl FileResolver {
    pub fn new(root: impl AsRef<std::path::Path>) -> Result<Self, std::io::Error> {
        Ok(Self {
            root: root.as_ref().canonicalize()?,
            paths: Default::default(),
        })
    }
}
impl SourceResolver for FileResolver {
    fn source_name(&self, name: &str) -> String {
        self.paths.get(name).cloned().unwrap_or_else(|| name.into())
    }
    fn source(&mut self, name: &str) -> Result<Option<String>, String> {
        let mut relative = std::path::PathBuf::new();
        for part in name.split('.') {
            if part.is_empty() || !part.chars().all(|c| c == '_' || c.is_alphanumeric()) {
                return Err("invalid checked module name".into());
            }
            relative.push(part);
        }
        let file = self.root.join(&relative).with_extension("py");
        let package = self.root.join(relative).join("__init__.py");
        let candidate = if file.is_file() {
            file
        } else if package.is_file() {
            package
        } else {
            return Ok(None);
        };
        let path = candidate.canonicalize().map_err(|e| e.to_string())?;
        if !path.starts_with(&self.root) {
            return Err(format!("checked module escapes source root: {name}"));
        }
        if path.metadata().map_err(|e| e.to_string())?.len() > 1_000_000 {
            return Err(format!("source exceeds frontend size limit: {name}"));
        }
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        self.paths.insert(name.into(), path.display().to_string());
        Ok(Some(source))
    }
}
