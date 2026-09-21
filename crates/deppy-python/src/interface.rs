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
    Inductive,
    Constructor,
}

#[derive(Clone, Debug)]
pub struct InductiveMetadata {
    pub id: u64,
    pub constructor_index: Option<usize>,
    pub declaration: deppy_core::DataDecl,
}
#[derive(Clone, Debug)]
pub struct InterfaceEntry {
    pub id: DefId,
    pub ty: Tm,
    pub kind: DeclarationKind,
    pub constructor: Option<DefId>,
    /// Opaque, kernel-checked specification theorem in this same snapshot.
    pub verified_spec: Option<DefId>,
    pub inductive: Option<InductiveMetadata>,
    /// Checked projection functions in the same kernel snapshot.
    pub projections: BTreeMap<String, Tm>,
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
        data_entries: &BTreeMap<String, (u64, Option<usize>)>,
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
                let inductive =
                    data_entries
                        .get(name)
                        .map(|(id, constructor_index)| InductiveMetadata {
                            id: *id,
                            constructor_index: *constructor_index,
                            declaration: kernel
                                .data_declaration(*id)
                                .expect("checked inductive family")
                                .clone(),
                        });
                let kind = if let Some(data) = &inductive {
                    if data.constructor_index.is_some() {
                        DeclarationKind::Constructor
                    } else {
                        DeclarationKind::Inductive
                    }
                } else if constructor.is_some() {
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
                        verified_spec: None,
                        inductive,
                        projections: BTreeMap::new(),
                        axiom_dependencies: dependencies[name].clone(),
                    },
                )
            })
            .collect();
        Self { kernel, exports }
    }
    pub(crate) fn set_verified_spec(&mut self, name: &str, id: DefId) {
        if let Some(entry) = self.exports.get_mut(name) {
            entry.verified_spec = Some(id);
        }
    }
    pub(crate) fn set_projections(&mut self, name: &str, projections: BTreeMap<String, Tm>) {
        if let Some(entry) = self.exports.get_mut(name) {
            entry.projections = projections;
        }
    }
}
