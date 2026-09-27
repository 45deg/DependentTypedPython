use deppy_python::{check_module, Target};
const LIST: &str = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Type, Nat, induct, Eq, refl\n@inductive\nclass List[A: Type]:\n    @constructor\n    def Nil() -> List[A]: ...\n    @constructor\n    def Cons(head: A, tail: List[A]) -> List[A]: ...\n";

#[test]
fn generic_coverage_termination_and_metadata() {
    let body = "\n@dependent\ndef head[A: Type](xs: List[A], fallback: A) -> A:\n    match xs:\n        case Nil():\n            return fallback\n        case Cons(h, t):\n            return h\n";
    let checked = check_module(&format!("{LIST}{body}"), Target::Python314).unwrap();
    let exports = checked.interface.exports();
    assert_eq!(
        exports["List"].kind,
        deppy_python::DeclarationKind::Inductive
    );
    assert_eq!(
        exports["Cons"].kind,
        deppy_python::DeclarationKind::Constructor
    );
    let info = exports["Cons"].inductive.as_ref().unwrap();
    assert_eq!(info.constructor_index, Some(1));
    assert_eq!(info.declaration.parameters.len(), 1);
    assert_eq!(info.declaration.constructors.len(), 2);
    assert!(check_module(
        &format!("{LIST}{}", body.replace("case Cons(h, t):", "case Nil():")),
        Target::Python314
    )
    .is_err());
    assert!(check_module(
        &format!(
            "{LIST}{}",
            body.replace("        case Cons(h, t):\n            return h\n", "")
        ),
        Target::Python314
    )
    .is_err());
}

#[test]
fn goals_display_general_family_names() {
    let source = format!("{LIST}\n@dependent\ndef unfinished[A: Type](xs: List[A]) -> List[A]:\n    return hole('xs')\n").replace("Nat, induct, Eq, refl", "Nat, induct, Eq, refl, hole");
    let analysis = deppy_python::analyze_module(&source, Target::Python314);
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    assert_eq!(analysis.goals[0].expected, "List[A]");
}

#[test]
fn imported_constructor_aliases_share_nominal_identity() {
    let library = LIST.to_owned();
    let left = "from __future__ import annotations\nfrom base import List, Nil, Cons\n".to_owned();
    let right = "from __future__ import annotations\nfrom base import List, Nil, Cons\n".to_owned();
    let mut resolver = |name: &str| {
        Ok(match name {
            "base" => Some(library.clone()),
            "left" => Some(left.clone()),
            "right" => Some(right.clone()),
            _ => None,
        })
    };
    let root = "from __future__ import annotations\nfrom deppy import dependent, Nat\nfrom left import List as L, Nil as N\nfrom right import List as R, Cons as C\n@dependent\ndef value() -> R[Nat]:\n    return C(0, N[Nat]())\n";
    deppy_python::check_module_with_resolver(root, Target::Python314, &mut resolver)
        .unwrap_or_else(|e| panic!("{e}"));
}
