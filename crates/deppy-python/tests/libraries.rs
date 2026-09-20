use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, check_module_with_resolver, Target};
const TARGET: Target = Target::Python314;
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, axiom, Type, Nat, Z, S, Pi, ImplicitPi, Eq, refl, J, nat_elim, vec_elim, fin_elim, Fin, FZ, FS, Vec, vnil, vcons, lam, implicit_lam, ann, record, record_elim\n";
fn source(body: &str) -> String {
    format!("{HEADER}{body}")
}
fn nat(n: usize) -> E {
    (0..n).fold(E::Zero, |n, _| n.succ())
}

#[test]
fn public_modules_group_builtins_and_checked_library_definitions() {
    let source = r#"from __future__ import annotations
from deppy.core import dependent, Type
from deppy.nat import Nat, Z, S
from deppy.equality import Eq, refl, sym
from deppy.sigma import Sigma, Pair
from deppy.fin import Fin, FZ
from deppy.vectors import Vec, VNil
from deppy.records import record

@record
class Box[A: Type]:
    value: A

@dependent
def sample(n: Nat) -> Sigma[Nat, lambda k: Eq[Nat, k, k]]:
    return Pair(n, sym(refl(n)))

@dependent
def empty() -> Vec[Nat, Z()]:
    return VNil()

@dependent
def first() -> Fin[S(Z())]:
    return FZ(Z())

@dependent
def boxed(n: Nat) -> Box[Nat]:
    return Box[Nat](n)
"#;
    let checked = check_module(source, TARGET).unwrap();
    assert_eq!(checked.definitions.len(), 5);
}

#[test]
fn top_level_is_the_prelude_and_there_is_no_prelude_submodule() {
    let source = r#"from __future__ import annotations
from deppy import dependent, Nat, Eq, refl, sym

@dependent
def symmetric(n: Nat) -> Eq[Nat, n, n]:
    return sym(refl(n))
"#;
    check_module(source, TARGET).unwrap();
    assert!(check_module(
        &source.replace("from deppy import", "from deppy.prelude import"),
        TARGET
    )
    .is_err());
}

#[test]
fn p0_math_library_shares_types_and_computes() {
    let source = r#"from __future__ import annotations
from deppy import dependent, Type, Nat, Eq, refl
from deppy.nat import add, mul
from deppy.data import Decidable, Yes
from deppy.logic import Decidable as LogicalDecision
from deppy.lists import List, Nil, Cons, length, filter
from deppy.nat_order import LE, LEZero, LESucc, LT, le_refl, le_trans

@dependent
def same_decision[P: Type](d: Decidable[P]) -> LogicalDecision[P]:
    return d

@dependent
def keep(n: Nat) -> Decidable[Eq[Nat, n, n]]:
    return Yes(refl(n))

@dependent
def arithmetic() -> Eq[Nat, add(2, mul(3, 2)), 8]:
    return refl(8)

@dependent
def list_length() -> Eq[Nat, length(Cons(1, Cons(2, Nil[Nat]()))), 2]:
    return refl(2)

@dependent
def filtered() -> Eq[List[Nat], filter[Nat, lambda n: Eq[Nat, n, n]](keep, Cons(1, Cons(2, Nil[Nat]()))), Cons(1, Cons(2, Nil[Nat]()))]:
    return refl(Cons(1, Cons(2, Nil[Nat]())))

@dependent
def ordered() -> LE[1, 3]:
    return le_trans(LESucc(0, 1, LEZero(1)), 3, LESucc(1, 2, LESucc(0, 1, LEZero(1))))

@dependent
def strict() -> LT(1, 3):
    return LESucc(1, 2, LESucc(0, 1, LEZero(1)))
"#;
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    for name in ["arithmetic", "list_length", "filtered"] {
        let id = checked
            .definitions
            .iter()
            .find(|(definition, _, _)| definition == name)
            .unwrap()
            .1;
        assert!(matches!(
            checked
                .elaborator
                .kernel()
                .normalize(&Term::Global(id).arc())
                .unwrap()
                .as_ref(),
            Term::Refl { .. }
        ));
    }
}

#[test]
fn primitives_lambdas_and_higher_universes_compute() {
    let s = source(
        r#"
@dependent
def add(n: Nat, m: Nat) -> Nat:
    return nat_elim(0, lambda k: Nat, m, lambda k, ih: S(ih), n)
@dependent
def rank(n: Nat, i: Fin[n]) -> Nat:
    return fin_elim(0, lambda size, index: Nat, lambda k: 0, lambda k, j, ih: S(ih), n, i)
@dependent
def length[A: Type](n: Nat, xs: Vec[A, n]) -> Nat:
    return vec_elim(0, A, lambda size, ys: Nat, 0, lambda k, head, tail, ih: S(ih), n, xs)
@dependent
def apply_id(n: Nat) -> Nat:
    helper = lam(Nat, lambda x: x)
    annotated = ann(lambda x: helper(x), Pi[Nat, lambda x: Nat])
    return annotated(n)
@dependent
def implicit_proof() -> ImplicitPi[Nat, lambda n: Eq[Nat, n, n]]:
    return implicit_lam(Nat, lambda n: refl(n))
@dependent
def use_implicit(n: Nat) -> Eq[Nat, n, n]:
    return implicit_proof[n]
@dependent
def types() -> Vec[Type, 1]:
    return vcons(Type, 0, Nat, vnil(Type))
@dependent
def sym_type(x: Type, y: Type, p: Eq[Type, x, y]) -> Eq[Type, y, x]:
    return J(1, Type, x, lambda end, proof: Eq[Type, end, x], refl(x), y, p)
@dependent
def higher_proof() -> Eq[Type, Nat, Nat]:
    return sym_type(Nat, Nat, refl(Nat))
"#,
    );
    let m = check_module(&s, TARGET).unwrap();
    let e = m.elaborator;
    for (term, expected) in [
        (E::name("add").app(nat(2)).app(nat(3)), nat(5)),
        (E::name("apply_id").app(nat(4)), nat(4)),
        (
            E::name("rank")
                .app(nat(2))
                .app(E::fs(nat(1), E::fz(nat(0)))),
            nat(1),
        ),
        (
            E::name("length")
                .app(nat(1))
                .app(E::vcons(E::Nat, nat(0), nat(5), E::vnil(E::Nat))),
            nat(1),
        ),
        (E::name("use_implicit").app(nat(2)), nat(2).refl()),
        (E::name("higher_proof"), E::Nat.refl()),
    ] {
        let actual = e.infer(&term).unwrap();
        let expected = e.infer(&expected).unwrap();
        assert_eq!(e.kernel().normalize(&actual.term).unwrap(), expected.term);
    }
}

#[test]
fn record_elimination_proves_eta_without_a_kernel_eta_rule() {
    let s = source(
        r#"
@record
class Box[A: Type]:
    length: Nat
    value: Vec[A, self.length]
@dependent
def eta[A: Type](box: Box[A]) -> Eq[Box[A], Box[A](box.length, box.value), box]:
    return record_elim(0, lambda b: Eq[Box[A], Box[A](b.length, b.value), b], lambda n, xs: refl(Box[A](n, xs)), box)
@dependent
def sample(n: Nat) -> Eq[Box[Nat], Box[Nat](0, vnil(Nat)), Box[Nat](0, vnil(Nat))]:
    return eta(Box[Nat](0, vnil(Nat)))
"#,
    );
    let m = check_module(&s, TARGET).unwrap();
    let proof = m.elaborator.infer(&E::name("sample").app(nat(0))).unwrap();
    assert!(matches!(
        m.elaborator
            .kernel()
            .normalize(&proof.term)
            .unwrap()
            .as_ref(),
        deppy_core::Term::Refl { .. }
    ));
    assert!(check_module(
        &s.replace("lambda n, xs: refl(Box[A](n, xs))", "lambda n, xs: refl(n)"),
        TARGET
    )
    .is_err());
}

#[test]
fn checked_libraries_alias_reexport_and_namespace_their_definitions() {
    let left = source("@dependent\ndef same(n: Nat) -> Nat:\n    return S(n)\n");
    let right = source("@dependent\ndef same(n: Nat) -> Nat:\n    return n\n");
    let reexport = "from __future__ import annotations\nfrom left import same as again\n";
    let main = source("from left import same as inc\nfrom right import same\nfrom facade import again\n@dependent\ndef run(n: Nat) -> Nat:\n    return again(inc(same(n)))\n");
    let mut resolver = |name: &str| {
        Ok(match name {
            "left" => Some(left.clone()),
            "right" => Some(right.clone()),
            "facade" => Some(reexport.into()),
            _ => None,
        })
    };
    let m = check_module_with_resolver(&main, TARGET, &mut resolver).unwrap();
    assert_eq!(m.definitions.len(), 1);
    let got = m.elaborator.infer(&E::name("run").app(nat(0))).unwrap();
    let expected = m.elaborator.infer(&nat(2)).unwrap();
    assert_eq!(
        m.elaborator.kernel().normalize(&got.term).unwrap(),
        expected.term
    );
    assert!(check_module(&main, TARGET).is_err());
}

#[test]
fn imported_records_preserve_nominal_identity() {
    let lib = source("@record\nclass Box[A: Type]:\n    value: A\n");
    let main = source("from left import Box as L\nfrom right import Box as R\n@dependent\ndef keep(n: Nat) -> L[Nat]:\n    return L[Nat](n)\n");
    let mut resolver = |_: &str| Ok(Some(lib.clone()));
    check_module_with_resolver(&main, TARGET, &mut resolver).unwrap();
    assert!(check_module_with_resolver(
        &main.replace("return L[Nat](n)", "return R[Nat](n)"),
        TARGET,
        &mut resolver
    )
    .is_err());
}

#[test]
fn invalid_import_graphs_and_unchecked_names_are_rejected() {
    let main =
        source("from lib import value\n@dependent\ndef use(n: Nat) -> Nat:\n    return value(n)\n");
    for lib in [
        "from __future__ import annotations\nfrom lib import value\n",
        "from __future__ import annotations\ndef value(n):\n    return n\n",
        "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent\ndef value(n: Nat) -> Nat:\n    return Nat\n",
    ] {
        let mut resolver = |_: &str| Ok(Some(lib.into()));
        assert!(check_module_with_resolver(&main, TARGET, &mut resolver).is_err());
    }
    let mut resolver = |_: &str| {
        Ok(Some(source(
            "@dependent\ndef value(n: Nat) -> Nat:\n    return n\n",
        )))
    };
    for bad in [
        main.replace("import value", "import *"),
        main.replace("from lib", "from .lib"),
        main.replace("return value(n)", "return missing(n)"),
    ] {
        assert!(check_module_with_resolver(&bad, TARGET, &mut resolver).is_err());
    }
}

#[test]
fn axioms_are_tracked_through_libraries() {
    let lib = source("@axiom\ndef assumption(n: Nat) -> Eq[Nat, n, 0]:\n    ...\n@axiom\ndef unused() -> Nat:\n    ...\n");
    let main = source("from assumptions import assumption\nfrom deppy.equality import sym\n@dependent\ndef theorem(n: Nat) -> Eq[Nat, 0, n]:\n    return sym(assumption(n))\n@dependent\ndef clean(n: Nat) -> Eq[Nat, n, n]:\n    return refl(n)\n");
    let mut resolver = |_: &str| Ok(Some(lib.clone()));
    let m = check_module_with_resolver(&main, TARGET, &mut resolver).unwrap();
    assert_eq!(
        m.axiom_dependencies["theorem"],
        vec!["assumptions.assumption"]
    );
    assert!(m.axiom_dependencies["clean"].is_empty());
    let bad = source("@axiom\ndef assumed() -> Eq[Nat, 0, 1]:\n    ...\n@dependent\ndef bogus() -> Eq[Nat, 0, 1]:\n    return refl(0)\n");
    assert!(check_module(&bad, TARGET).is_err());
    for body in ["return refl(0)", "pass", "...\n    return refl(0)"] {
        assert!(check_module(
            &source(&format!(
                "@axiom\ndef bad() -> Eq[Nat, 0, 0]:\n    {body}\n"
            )),
            TARGET
        )
        .is_err());
    }
    assert!(check_module(&source("@dependent\ndef hole() -> Nat:\n    ...\n"), TARGET).is_err());
    assert!(check_module(&source("@axiom\ndef bad() -> 0:\n    ...\n"), TARGET).is_err());
}

#[test]
fn primitive_calls_reject_bad_motives_levels_and_annotations() {
    for expression in [
        "nat_elim(0, lambda n: Type, Nat, lambda k, ih: Nat, n)",
        "nat_elim(n, lambda k: Nat, 0, lambda k, ih: ih, n)",
        "nat_elim(0, lambda k: Nat, 0, lambda k, ih: Type, n)",
        "J(0, Nat, 0, lambda end, p: Eq[Nat, 0, end], refl(0), 1, refl(1))",
        "ann(n, Type)",
        "lam(Nat, lambda x, y: x)",
        "fin_elim(0, lambda k, i: Nat, lambda k: 0, lambda k, j, ih: ih, 0, FZ(0))",
    ] {
        assert!(
            check_module(
                &source(&format!(
                    "@dependent\ndef bad(n: Nat) -> Nat:\n    return {expression}\n"
                )),
                TARGET
            )
            .is_err(),
            "{expression}"
        );
    }
}

#[test]
fn explicit_reverse_proof_uses_only_python_library_and_eliminators() {
    let m = check_module(include_str!("../examples/reverse_explicit.py"), TARGET).unwrap();
    assert!(m.axiom_dependencies["reverse_get"].is_empty());
    let xs = E::vcons(
        E::Nat,
        nat(1),
        nat(3),
        E::vcons(E::Nat, nat(0), nat(7), E::vnil(E::Nat)),
    );
    for (i, value) in [(E::fz(nat(1)), 3), (E::fs(nat(1), E::fz(nat(0))), 7)] {
        let proof = m
            .elaborator
            .infer(&E::name("reverse_get").app(nat(2)).app(xs.clone()).app(i))
            .unwrap();
        let want = m.elaborator.infer(&nat(value).refl()).unwrap();
        assert_eq!(
            m.elaborator.kernel().normalize(&proof.term).unwrap(),
            want.term
        );
    }
}
