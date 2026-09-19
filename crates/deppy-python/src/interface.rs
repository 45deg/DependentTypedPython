//! Read-only exports tied to the exact kernel environment that checked them.
use crate::Span;
use deppy_core::{DefId, Kernel, Tm, Transparency};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationKind {
    Definition,
    Opaque,
    Axiom,
    Record,
}

#[derive(Clone, Debug)]
pub struct InterfaceEntry {
    pub id: DefId,
    pub ty: Tm,
    pub kind: DeclarationKind,
    pub constructor: Option<DefId>,
    pub axiom_dependencies: Vec<String>,
}

pub struct CheckedInterface {
    kernel: Kernel,
    exports: BTreeMap<String, InterfaceEntry>,
}
impl CheckedInterface {
    pub fn exports(&self) -> &BTreeMap<String, InterfaceEntry> {
        &self.exports
    }
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }
    pub(crate) fn from_checked(
        elaborator: &deppy_elab::Elaborator,
        definitions: &[(String, DefId, Span)],
        constructors: &[(String, DefId, Span)],
        dependencies: &BTreeMap<String, Vec<String>>,
    ) -> Self {
        let kernel = elaborator.kernel().clone();
        let exports = definitions
            .iter()
            .map(|(name, id, _)| {
                // These IDs were produced by this elaborator, not by interface consumers.
                let definition = kernel
                    .definition(*id)
                    .expect("registered checked definition");
                let constructor = constructors
                    .iter()
                    .find(|(n, _, _)| n == name)
                    .map(|(_, id, _)| *id);
                let kind = if constructor.is_some() {
                    DeclarationKind::Record
                } else if definition.body.is_none() {
                    DeclarationKind::Axiom
                } else if definition.transparency == Transparency::Opaque {
                    DeclarationKind::Opaque
                } else {
                    DeclarationKind::Definition
                };
                (
                    name.clone(),
                    InterfaceEntry {
                        id: *id,
                        ty: definition.ty.clone(),
                        kind,
                        constructor,
                        axiom_dependencies: dependencies[name].clone(),
                    },
                )
            })
            .collect();
        Self { kernel, exports }
    }
}
