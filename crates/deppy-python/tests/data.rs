use deppy_core::Term;
use deppy_python::{check_module, Target};
const LIST: &str = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Type, Nat, induct, Eq, refl\n@inductive\nclass List[A: Type]:\n    @constructor\n    def Nil() -> List[A]: ...\n    @constructor\n    def Cons(head: A, tail: List[A]) -> List[A]: ...\n";
#[test]
fn fixed_and_compound_indices_omit_impossible_branches() {
    let source = r#"from __future__ import annotations
from deppy import dependent, Type, Nat as Count, Eq, refl
from deppy.naturals import Nat, Z, S
from deppy.indexed import IVec, INil, ICons
@dependent(decreases='xs')
def head[A: Type](n: Nat, xs: IVec[A, S(n)]) -> A:
    match xs:
        case ICons(k, h, tail):
            return h
@dependent(decreases='xs')
def empty[A: Type](xs: IVec[A, Z()]) -> Count:
    match xs:
        case INil():
            return 0
@dependent(decreases='xs')
def second[A: Type](xs: IVec[A, S(S(Z()))]) -> A:
    match xs:
        case ICons(k, h, tail):
            match tail:
                case ICons(j, next, rest):
                    return head(Z(), tail)
@dependent(decreases='xs')
def last[A: Type](n: Nat, xs: IVec[A, S(n)]) -> A:
    match xs:
        case ICons(k, h, tail):
            match tail:
                case INil():
                    return h
                case ICons(j, next, rest):
                    return last(j, tail)
@dependent
def proof() -> Eq[Count, second(ICons(S(Z()), 7, ICons(Z(), 9, INil[Count]()))), 9]:
    return refl(9)
@dependent
def last_proof() -> Eq[Count, last(S(Z()), ICons(S(Z()), 7, ICons(Z(), 9, INil[Count]()))), 9]:
    return refl(9)
"#;
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace("return head(Z(), tail)", "return head(S(Z()), tail)"),
        Target::Python314
    )
    .is_err());
}
#[test]
fn nested_general_matches_compute_and_keep_coverage_checks() {
    let source = format!("{LIST}\n@dependent\ndef classify[A: Type](xs: List[A]) -> Nat:\n    match xs:\n        case Nil():\n            return 0\n        case Cons(h, t):\n            match t:\n                case Nil():\n                    return 1\n                case Cons(j, rest):\n                    match rest:\n                        case Nil():\n                            return 2\n                        case Cons(k, tail):\n                            return 3\n@dependent\ndef proof() -> Eq[Nat, classify(Cons(0, Cons(0, Nil()))), 2]:\n    return refl(2)\n");
    check_module(&source, Target::Python314).unwrap();
    let missing = source.replace(
        "                        case Cons(k, tail):\n                            return 3\n",
        "",
    );
    assert!(check_module(&missing, Target::Python314).is_err());
}
#[test]
fn constructor_matrix_supports_nested_recursion_and_ordered_wildcards() {
    let source = format!("{LIST}\n@dependent\ndef pairs[A: Type](xs: List[A]) -> Nat:\n    match xs:\n        case Nil():\n            return 0\n        case Cons(_, Nil()):\n            return 0\n        case Cons(_, Cons(_, rest)):\n            return pairs(rest)\n@dependent\ndef choose[A: Type](xs: List[A]) -> Nat:\n    match xs:\n        case Cons(_, Cons(_, Nil())):\n            return 2\n        case Cons(_, _):\n            return 1\n        case Nil():\n            return 0\n@dependent\ndef proof() -> Eq[Nat, pairs(Cons(0, Cons(0, Cons(0, Cons(0, Nil()))))), 0]:\n    return refl(0)\n@dependent\ndef selected() -> Eq[Nat, choose(Cons(0, Cons(0, Nil()))), 2]:\n    return refl(2)\n");
    check_module(&source, Target::Python314).unwrap();
    let bad = source.replace("return pairs(rest)", "return pairs(xs)");
    assert!(check_module(&bad, Target::Python314).is_err());
}
#[test]
fn python_list_induction_computes_and_checks_equality() {
    let source = format!("{LIST}\n@dependent\ndef length[A: Type](xs: List[A]) -> Nat:\n    return induct(0, xs, lambda _: Nat, 0, lambda h, t, ih: 1)\n@dependent\ndef test() -> Eq[Nat, length(Cons(0, Nil())), 1]:\n    return refl(1)\n");
    let module = check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    let id = module
        .definitions
        .iter()
        .find(|(name, _, _)| name == "test")
        .unwrap()
        .1;
    assert!(matches!(
        module
            .elaborator
            .kernel()
            .normalize(&Term::Global(id).arc())
            .unwrap()
            .as_ref(),
        Term::Refl { .. }
    ));
}
#[test]
fn python_negative_recursion_is_rejected() {
    let source = "from __future__ import annotations\nfrom deppy import inductive, constructor, Pi, Nat\n@inductive\nclass Bad:\n    @constructor\n    def Mk(f: Pi[Bad, Nat]) -> Bad: ...\n";
    assert!(check_module(source, Target::Python314).is_err());
}

#[test]
fn structural_list_recursion_checks_and_computes() {
    let source = format!("{LIST}\n@dependent(decreases='xs')\ndef length[A: Type](xs: List[A]) -> Nat:\n    match xs:\n        case Nil():\n            return 0\n        case Cons(h, t):\n            return length(t)\n@dependent\ndef proof() -> Eq[Nat, length(Cons(0, Nil())), 0]:\n    return refl(0)\n");
    check_module(&source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn standard_libraries_check_four_list_theorems_and_indexed_get() {
    for source in [
        include_str!("../stdlib/deppy/data.py"),
        include_str!("../stdlib/deppy/equality.py"),
        include_str!("../stdlib/deppy/nat.py"),
        include_str!("../stdlib/deppy/nat_order.py"),
        include_str!("../stdlib/deppy/lists.py"),
        include_str!("../stdlib/deppy/indexed.py"),
        include_str!("../stdlib/deppy/naturals.py"),
    ] {
        let checked = check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
        assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    }
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, refl\nfrom deppy.indexed import IVec, INil, ICons, IFin, IFZ, IFS, get\nfrom deppy.naturals import Z, S\n@dependent\ndef first() -> Eq[Nat, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]())), IFZ(S(Z()))), 7]:\n    return refl(7)\n@dependent\ndef second() -> Eq[Nat, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Nat]())), IFS(S(Z()), IFZ(Z()))), 9]:\n    return refl(9)\n";
    let checked = check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    for (_, id, _) in &checked.definitions {
        assert!(matches!(
            checked
                .elaborator
                .kernel()
                .normalize(&Term::Global(*id).arc())
                .unwrap()
                .as_ref(),
            Term::Refl { .. }
        ));
    }
    assert!(check_module(
        &source.replace("IFS(S(Z()), IFZ(Z()))", "IFS(S(S(Z())), IFZ(S(Z())))"),
        Target::Python314
    )
    .is_err());
}

#[test]
fn dependent_declarations_accept_python_docstrings() {
    let source = r#"from __future__ import annotations
from deppy import inductive, constructor, dependent, Nat, Z, S, Eq, refl
@inductive
class Flag:
    """A documented proposition."""
    @constructor
    def On() -> Flag:
        """The sole constructor."""
        ...
@dependent
def identity(n: Nat) -> Nat:
    """Return :math:`n`."""
    return n
@dependent(decreases="n")
def proof(n: Nat) -> Eq[Nat, identity(n), n]:
    """Identity theorem."""
    match n:
        case Z():
            return refl(0)
        case S(k):
            return refl(S(k))
"#;
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn multiple_recursive_children_can_be_used_in_one_expression() {
    let source = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Nat, nat_elim, S, Eq, refl\n@dependent\ndef plus(n: Nat, m: Nat) -> Nat:\n    return nat_elim(0, lambda _: Nat, m, lambda k, ih: S(ih), n)\n@inductive\nclass Tree:\n    @constructor\n    def Leaf() -> Tree: ...\n    @constructor\n    def Node(left: Tree, right: Tree) -> Tree: ...\n@dependent(decreases='tree')\ndef size(tree: Tree) -> Nat:\n    match tree:\n        case Leaf():\n            return 1\n        case Node(left, right):\n            return plus(size(left), size(right))\n@dependent\ndef proof() -> Eq[Nat, size(Node(Leaf(), Node(Leaf(), Leaf()))), 3]:\n    return refl(3)\n";
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert!(check_module(
        &source.replace("size(left), size(right)", "size(tree), size(right)"),
        Target::Python314
    )
    .is_err());
}

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
fn indexed_absurd_rejects_inhabited_or_unknown_indices() {
    let prefix = "from __future__ import annotations\nfrom deppy import dependent, Nat, absurd\nfrom deppy.indexed import IFin\nfrom deppy.naturals import Nat as N, Z, S\n";
    for (params, bound) in [("", "Z()"), ("", "S(Z())"), ("n: N, ", "n")] {
        let source = format!("{prefix}@dependent\ndef impossible({params}i: IFin[{bound}]) -> Nat:\n    return absurd(Nat, i)\n");
        assert_eq!(
            check_module(&source, Target::Python314).is_ok(),
            bound == "Z()"
        );
    }
}

#[test]
fn higher_universe_inductive_and_negative_alias_checks() {
    let source = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Type, Pi, Nat\n@dependent\ndef Negative(T: Type) -> Type:\n    return Pi[T, lambda _: Nat]\n@inductive\nclass Bad:\n    @constructor\n    def Mk(f: Negative(Bad)) -> Bad: ...\n";
    let error = match check_module(source, Target::Python314) {
        Err(e) => e,
        Ok(_) => panic!("negative alias accepted"),
    };
    assert!(error.message.contains("positive"), "{error}");
    let high = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Type, Nat\n@inductive(level=1)\nclass Box:\n    @constructor\n    def Pack(T: Type) -> Box: ...\n@dependent\ndef value() -> Box:\n    return Pack(Nat)\n";
    assert!(check_module(high, Target::Python314).is_ok());
    assert!(check_module(&high.replace("(level=1)", ""), Target::Python314).is_err());
}

#[test]
fn indexed_structural_recursion_and_pattern_wildcards() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Type, Nat as Count, Eq, refl, S as Succ\nfrom deppy.naturals import Nat, Z, S\nfrom deppy.indexed import IVec, INil, ICons\n@dependent(decreases='xs')\ndef length[A: Type](n: Nat, xs: IVec[A, n]) -> Count:\n    match xs:\n        case INil():\n            return 0\n        case ICons(k, _, tail):\n            return Succ(length(k, tail))\n@dependent\ndef proof() -> Eq[Count, length(S(Z()), ICons(Z(), 7, INil[Count]())), 1]:\n    return refl(1)\n";
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn demonstration_nat_cannot_index_canonical_naturals() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat\nfrom deppy.nat import add\nfrom deppy.naturals import Nat as DemoNat\n@dependent\ndef wrong(n: DemoNat) -> Nat:\n    return add(n, 0)\n";
    assert!(check_module(source, Target::Python314).is_err());
}

#[test]
fn dependent_nested_matches_implement_indexed_get() {
    let source = r#"from __future__ import annotations
from deppy import dependent, Type, Nat as Count, Eq, refl, absurd
from deppy.naturals import Nat, Z, S
from deppy.indexed import IVec, INil, ICons, IFin, IFZ, IFS
@dependent(decreases='xs')
def get[A: Type, n: Nat](xs: IVec[A, n], i: IFin[n]) -> A:
    match xs:
        case INil():
            return absurd(A, i)
        case ICons(k, head, tail):
            match i:
                case IFZ(j):
                    return head
                case IFS(j, pred):
                    return get(tail, pred)
@dependent
def proof() -> Eq[Count, get(ICons(S(Z()), 7, ICons(Z(), 9, INil[Count]())), IFS(S(Z()), IFZ(Z()))), 9]:
    return refl(9)
"#;
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn goals_display_general_family_names() {
    let source = format!("{LIST}\n@dependent\ndef unfinished[A: Type](xs: List[A]) -> List[A]:\n    return hole('xs')\n").replace("Nat, induct, Eq, refl", "Nat, induct, Eq, refl, hole");
    let analysis = deppy_python::analyze_module(&source, Target::Python314);
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    assert_eq!(analysis.goals[0].expected, "List[A]");
}

#[test]
fn positive_function_field_computes_through_elaboration() {
    let source = "from __future__ import annotations\nfrom deppy import inductive, constructor, dependent, Pi, Nat, S, induct, Eq, refl\n@inductive\nclass Tree:\n    @constructor\n    def Leaf() -> Tree: ...\n    @constructor\n    def Node(children: Pi[Nat, lambda _: Tree]) -> Tree: ...\n@dependent\ndef depth(tree: Tree) -> Nat:\n    return induct(0, tree, lambda _: Nat, 0, lambda children, ih: S(ih(0)))\n@dependent\ndef proof() -> Eq[Nat, depth(Node(lambda n: Leaf())), 1]:\n    return refl(1)\n";
    check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
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

#[test]
fn list_theorems_normalize_on_small_values_and_reject_false_claims() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, S, Eq\nfrom deppy.lists import List, Nil, Cons, append, map, reverse, append_assoc, map_identity, map_composition, reverse_involution\n@dependent\ndef assoc() -> Eq[List[Nat], append(append(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]())), Nil[Nat]()), append(Cons(0, Nil[Nat]()), append(Cons(1, Nil[Nat]()), Nil[Nat]()))]:\n    return append_assoc(Cons(0, Nil[Nat]()), Cons(1, Nil[Nat]()), Nil[Nat]())\n@dependent\ndef identity() -> Eq[List[Nat], map(lambda x: x, Cons(0, Nil[Nat]())), Cons(0, Nil[Nat]())]:\n    return map_identity(Cons(0, Nil[Nat]()))\n@dependent\ndef composition() -> Eq[List[Nat], map(lambda x: S(x), map(lambda x: S(x), Cons(0, Nil[Nat]()))), Cons(2, Nil[Nat]())]:\n    return map_composition(lambda x: S(x), lambda x: S(x), Cons(0, Nil[Nat]()))\n@dependent\ndef involution() -> Eq[List[Nat], reverse(reverse(Cons(0, Cons(1, Nil[Nat]())))), Cons(0, Cons(1, Nil[Nat]()))]:\n    return reverse_involution(Cons(0, Cons(1, Nil[Nat]())))\n";
    let checked = check_module(source, Target::Python314).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(checked.definitions.len(), 4);
    for (_, id, _) in &checked.definitions {
        let proof = checked
            .elaborator
            .kernel()
            .normalize(&Term::Global(*id).arc())
            .unwrap();
        assert!(matches!(proof.as_ref(), Term::Refl { .. }));
    }
    assert!(check_module(
        &source.replace("Cons(2, Nil[Nat]())", "Cons(1, Nil[Nat]())"),
        Target::Python314
    )
    .is_err());
}
