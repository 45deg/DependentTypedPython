use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, check_module_with_resolver, DeclarationKind, Target};
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
from deppy import dependent, Type, Sigma, Pair, record
from deppy.nat import Nat, Z, S
from deppy.equality import Eq, refl, sym
from deppy.fin import Fin, FZ
from deppy.vectors import Vec, VNil

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
    for module in ["core", "logic", "records", "sigma"] {
        let source = format!("from deppy.{module} import missing\n");
        let error = match check_module(&source, TARGET) {
            Ok(_) => panic!("removed module deppy.{module} was accepted"),
            Err(error) => error,
        };
        assert!(
            error.to_string().contains("unknown standard module"),
            "{module}: {error}"
        );
    }
}

#[test]
fn p0_math_library_shares_types_and_computes() {
    let source = r#"from __future__ import annotations
from deppy import dependent, Type, Nat, Eq, refl
from deppy.nat import add, mul
from deppy.data import Decidable, Yes
from deppy.data import Decidable as LogicalDecision
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
fn p0_nat_boolean_comparisons_are_axiom_free() {
    let checked = check_module(include_str!("../stdlib/deppy/nat_bool.py"), TARGET).unwrap();
    for name in [
        "equal",
        "nat_eq",
        "equal_nat_eq",
        "equal_true",
        "nat_eq_true",
    ] {
        assert!(checked.interface.exports().contains_key(name), "{name}");
        assert!(checked.axiom_dependencies[name].is_empty(), "{name}");
    }
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn p0_verified_compatibility_names_are_real_declarations() {
    let checked = check_module(include_str!("../stdlib/deppy/verified.py"), TARGET).unwrap();
    for name in [
        "select", "bool_not", "bool_eq", "nat_le", "nat_lt", "nat_eq",
    ] {
        assert_eq!(
            checked.interface.exports()[name].kind,
            DeclarationKind::Definition,
            "{name}"
        );
    }
    for name in [
        "select_post_eq",
        "decision_true",
        "false_true_elim",
        "true_false_elim",
        "nat_eq_true",
        "nat_lt_not_false",
        "nat_le_refl_true",
        "nat_lt_true",
        "nat_le_true",
        "nat_lt_false_zero",
        "pred_lt_true",
        "lt_le_bound",
    ] {
        assert_eq!(
            checked.interface.exports()[name].kind,
            DeclarationKind::Opaque,
            "{name}"
        );
    }
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
}

#[test]
fn p0_removal_imports_share_evidence_and_reject_bad_indices() {
    let source = r#"from __future__ import annotations
from deppy import theorem, dependent, Nat, Eq, refl, S
from deppy.data import Decidable, Yes
from deppy.lists import List, Nil, Cons, Removal as ListRemoval, RemoveHere as ListHere, removal_length, length, count
from deppy.finite import Removal as FiniteRemoval, RemoveHere as FiniteHere, RemoveThere as FiniteThere, removal_present, removal_count

@dependent
def decide(n: Nat) -> Decidable[Eq[Nat, n, n]]:
    return Yes(refl(n))

@theorem
def shared(r: ListRemoval[Nat, 1, Cons(1, Nil[Nat]()), Nil[Nat]()]) -> FiniteRemoval[Nat, 1, Cons(1, Nil[Nat]()), Nil[Nat]()]:
    return r

@theorem
def lists_to_finite() -> Eq[Nat, count[Nat, lambda n: Eq[Nat, n, n]](decide, Cons(1, Cons(1, Nil[Nat]()))), S(count[Nat, lambda n: Eq[Nat, n, n]](decide, Cons(1, Nil[Nat]())) )]:
    return removal_count[Nat, 1, Cons(1, Cons(1, Nil[Nat]())), Cons(1, Nil[Nat]()), lambda n: Eq[Nat, n, n]](decide, ListHere[Nat, 1](Cons(1, Nil[Nat]())))

@theorem
def finite_to_lists() -> Eq[Nat, length(Cons(1, Cons(1, Nil[Nat]()))), S(length(Cons(1, Nil[Nat]())))]:
    return removal_length(FiniteThere[Nat, 1](1, Cons(1, Nil[Nat]()), Nil[Nat](), FiniteHere[Nat, 1](Nil[Nat]())))

@theorem
def finite_constructor_in_lists() -> ListRemoval[Nat, 1, Cons(1, Nil[Nat]()), Nil[Nat]()]:
    return FiniteHere[Nat, 1](Nil[Nat]())
"#;
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let old_client = r#"from __future__ import annotations
from deppy import theorem, Nat
from deppy.lists import Nil, Cons
from deppy.finite import Removal, RemoveHere, find_removal
@theorem
def old_path() -> Removal[Nat, 1, Cons(1, Nil[Nat]()), Nil[Nat]()]:
    return RemoveHere[Nat, 1](Nil[Nat]())
"#;
    check_module(old_client, TARGET).unwrap();
    let invalid = format!(
        "{source}\n@theorem\ndef bad() -> ListRemoval[Nat, 1, Cons(1, Nil[Nat]()), Cons(1, Nil[Nat]())]:\n    return FiniteHere[Nat, 1](Nil[Nat]())\n"
    );
    assert!(check_module(&invalid, TARGET).is_err());
}

#[test]
fn p0_comparison_compatibility_preserves_open_and_closed_reduction() {
    let source = r#"from __future__ import annotations
from deppy import dependent, theorem, Nat, S, Eq, refl
from deppy.data import Bool, True_, False_
from deppy.bool import select, bool_not, bool_eq, negate
from deppy.nat_bool import nat_le, nat_eq, equal, equal_nat_eq
from deppy.verified import nat_eq as verified_nat_eq, bool_not as verified_bool_not, bool_eq as verified_bool_eq
from deppy.arithmetic import equal as arithmetic_equal

@dependent
def old_not(flag: Bool) -> Bool:
    return select[Bool](flag, True_(), False_())

@dependent
def old_nat_eq(n: Nat, m: Nat) -> Bool:
    return select[Bool](nat_le(n, m), False_(), nat_le(m, n))

@dependent
def old_bool_eq(left: Bool, right: Bool) -> Bool:
    return select[Bool](left, old_not(right), right)

@dependent
def open_bool(flag: Bool) -> Eq[Bool, old_not(flag), bool_not(flag)]:
    return refl(old_not(flag))

@dependent
def open_nat(n: Nat, m: Nat) -> Eq[Bool, old_nat_eq(n, m), nat_eq(n, m)]:
    return refl(old_nat_eq(n, m))

@dependent
def open_bool_eq(left: Bool, right: Bool) -> Eq[Bool, old_bool_eq(left, right), bool_eq(left, right)]:
    return refl(old_bool_eq(left, right))

@dependent
def old_paths(n: Nat, m: Nat, flag: Bool) -> Eq[Bool, verified_bool_not(flag), bool_not(flag)]:
    return refl(bool_not(flag))

@dependent
def old_nat_path(n: Nat, m: Nat) -> Eq[Bool, verified_nat_eq(n, m), nat_eq(n, m)]:
    return refl(nat_eq(n, m))

@dependent
def old_bool_path(left: Bool, right: Bool) -> Eq[Bool, verified_bool_eq(left, right), bool_eq(left, right)]:
    return refl(bool_eq(left, right))

@dependent
def select_false() -> Eq[Nat, select[Nat](False_(), 7, 9), 7]:
    return refl(7)

@dependent
def select_true() -> Eq[Nat, select[Nat](True_(), 7, 9), 9]:
    return refl(9)

@dependent
def arithmetic_path(n: Nat, m: Nat) -> Eq[Bool, arithmetic_equal(n, m), equal(n, m)]:
    return refl(equal(n, m))

@dependent
def closed_equal() -> Eq[Bool, equal(2, 2), True_()]:
    return refl(True_())

@dependent
def closed_unequal() -> Eq[Bool, nat_eq(2, 3), False_()]:
    return refl(False_())

@dependent
def structural_unequal() -> Eq[Bool, equal(2, 3), False_()]:
    return refl(False_())

@dependent
def order_equal() -> Eq[Bool, nat_eq(S(2), 3), True_()]:
    return refl(True_())

@theorem
def bridges(n: Nat, m: Nat, flag: Bool) -> Eq[Bool, equal(n, m), nat_eq(n, m)]:
    return equal_nat_eq(n, m)
"#;
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let neutral_negate = format!(
        "{source}\n@dependent\ndef compatible(flag: Bool) -> Eq[Bool, old_not(flag), negate(flag)]:\n    return refl(old_not(flag))\n"
    );
    check_module(&neutral_negate, TARGET).unwrap();
    let wrong = format!(
        "{source}\n@dependent\ndef wrong() -> Eq[Bool, nat_eq(1, 2), True_()]:\n    return refl(True_())\n"
    );
    assert!(check_module(&wrong, TARGET).is_err());
    let wrong_order = format!(
        "{source}\n@dependent\ndef wrong_order() -> Eq[Bool, nat_le(3, 1), True_()]:\n    return refl(True_())\n"
    );
    assert!(check_module(&wrong_order, TARGET).is_err());
}

#[test]
fn p0_documented_members_and_compatibility_paths_are_checked_imports() {
    let reference = include_str!("../../../docs/math-api.rst");
    let mut module = None;
    for line in reference.lines() {
        if let Some(path) = line
            .trim()
            .strip_prefix(".. deppy-api:: crates/deppy-python/stdlib/deppy/")
        {
            module = Some(path.trim_end_matches(".py"));
        } else if let Some(members) = line.trim().strip_prefix(":members: ") {
            let module = module.expect("members require a source module");
            let source = format!(
                "from __future__ import annotations\nfrom deppy.{module} import {}\n",
                members
            );
            check_module(&source, TARGET).unwrap_or_else(|e| panic!("deppy.{module}: {e}"));
        }
        if let Some(alias) = line.trim().strip_prefix("* - ``deppy.") {
            if let Some(qualified) = alias.strip_suffix("``") {
                let (module, name) = qualified.rsplit_once('.').unwrap();
                let source = format!(
                    "from __future__ import annotations\nfrom deppy.{module} import {name}\n"
                );
                check_module(&source, TARGET).unwrap_or_else(|e| panic!("deppy.{qualified}: {e}"));
            }
        }
    }
}

#[test]
fn math_lemmas_and_finite_carrier_are_axiom_free() {
    let source = r#"from __future__ import annotations
from deppy import dependent, theorem, Type, Pi, Sigma, Pair, Nat, Fin, FZ, FS, Vec, VNil, VCons, Eq, refl, absurd
from deppy.nat import add, mul, mul_comm, mul_assoc, mul_add_left
from deppy.nat_order import LE, LT, le_total, le_to_lt_succ, lt_succ_to_le, strong_induction, mul_le_mul_left, mul_le_mul_right, mul_left_cancel_pos
from deppy.data import Empty, Unit, Sum, Left, MkUnit, Decidable, Yes
from deppy.lists import List, Nil, Cons, Mem, NoDup, append, map, length, filter, reject, count, length_append, length_map, length_reverse, map_append, reverse as list_reverse, reverse_append, map_reverse, mem_append_cases, filter_mem, filter_nodup, map_nodup, length_filter_eq_count, length_filter_le, count_split
from deppy.fin import to_nat, to_nat_lt, to_nat_injective
from deppy.vectors import get, get_map, map as deppy_map, append as vec_append, append_left_index, append_right_index, get_append_left, get_append_right, reverse, mirror, reverse_get, mirror_involution, vec_extensional
from deppy.finite import Enumeration, finite_count, finite_all_decide, finite_any_decide, finite_search, bijection_enumeration, bijection_cardinality
from deppy.functions import Bijection, identity_bijection, inverse_bijection, compose_bijection, bijection_injective, bijection_surjective
from deppy.permutations import Permutation, PermSwap, perm_refl, perm_sym, perm_length, perm_mem, perm_nodup, perm_map

@theorem
def multiplication(a: Nat, b: Nat, c: Nat) -> Eq[Nat, mul(add(a, b), c), add(mul(a, c), mul(b, c))]:
    return mul_add_left(a, b, c)

@theorem
def multiplication_bound(n: Nat, m: Nat, k: Nat, p: LE[n, m]) -> LE[mul(k, n), mul(k, m)]:
    return mul_le_mul_left(k, p)

@theorem
def cancel_positive(k: Nat, n: Nat, m: Nat, positive: LT(0, k), equal: Eq[Nat, mul(k, n), mul(k, m)]) -> Eq[Nat, n, m]:
    return mul_left_cancel_pos(k, n, m, positive, equal)

@theorem
def compare(n: Nat, m: Nat) -> Sum[LE[n, m], LE[m, n]]:
    return le_total(n, m)

@theorem
def strong_refl(n: Nat) -> Eq[Nat, n, n]:
    return strong_induction[lambda k: Eq[Nat, k, k]](n, lambda k: lambda smaller: refl(k))

@theorem
def mapped_length[A: Type, B: Type](f: Pi[A, lambda _: B], xs: List[A]) -> Eq[Nat, length(map(f, xs)), length(xs)]:
    return length_map(f, xs)

@theorem
def reversed_append(xs: List[Nat], ys: List[Nat]) -> Eq[List[Nat], list_reverse(append(xs, ys)), append(list_reverse(ys), list_reverse(xs))]:
    return reverse_append(xs, ys)

@theorem
def mapped_reverse(f: Pi[Nat, lambda _: Nat], xs: List[Nat]) -> Eq[List[Nat], map(f, list_reverse(xs)), list_reverse(map(f, xs))]:
    return map_reverse(f, xs)

@theorem
def finite_bound(n: Nat, i: Fin[n]) -> LT(to_nat(n, i), n):
    return to_nat_lt(n, i)

@theorem
def finite_injective(n: Nat, i: Fin[n], j: Fin[n], equal: Eq[Nat, to_nat(n, i), to_nat(n, j)]) -> Eq[Fin[n], i, j]:
    return to_nat_injective(n, i, j, equal)

@theorem
def mirror_twice(n: Nat, i: Fin[n]) -> Eq[Fin[n], mirror(n, mirror(n, i)), i]:
    return mirror_involution(n, i)

@theorem
def mapped_get[A: Type, B: Type](n: Nat, f: Pi[A, lambda _: B], xs: Vec[A, n], i: Fin[n]) -> Eq[B, get(n, deppy_map(n, f, xs), i), f(get(n, xs, i))]:
    return get_map(n, f, xs, i)

@theorem
def vector_extensional(n: Nat, xs: Vec[Nat, n], ys: Vec[Nat, n], points: Pi[Fin[n], lambda i: Eq[Nat, get(n, xs, i), get(n, ys, i)]]) -> Eq[Vec[Nat, n], xs, ys]:
    return vec_extensional(n, xs, ys, points)

@theorem
def keep(n: Nat) -> Decidable[Eq[Nat, n, n]]:
    return Yes(refl(n))

@theorem
def filtered_length(xs: List[Nat]) -> Eq[Nat, length(filter[Nat, lambda n: Eq[Nat, n, n]](keep, xs)), count[Nat, lambda n: Eq[Nat, n, n]](keep, xs)]:
    return length_filter_eq_count[Nat, lambda n: Eq[Nat, n, n]](keep, xs)

@theorem
def filtered_partition(xs: List[Nat]) -> Eq[Nat, add(count[Nat, lambda n: Eq[Nat, n, n]](keep, xs), length(reject[Nat, lambda n: Eq[Nat, n, n]](keep, xs))), length(xs)]:
    return count_split[Nat, lambda n: Eq[Nat, n, n]](keep, xs)

@theorem
def filtered_unique(xs: List[Nat], unique: NoDup(xs)) -> NoDup(filter[Nat, lambda n: Eq[Nat, n, n]](keep, xs)):
    return filter_nodup[Nat, lambda n: Eq[Nat, n, n]](keep, xs, unique)

@theorem
def left_lookup(n: Nat, m: Nat, xs: Vec[Nat, n], ys: Vec[Nat, m], i: Fin[n]) -> Eq[Nat, get(add(n, m), vec_append(n, m, xs, ys), append_left_index(n, m, i)), get(n, xs, i)]:
    return get_append_left(n, m, xs, ys, i)

@theorem
def right_lookup(n: Nat, m: Nat, xs: Vec[Nat, n], ys: Vec[Nat, m], i: Fin[m]) -> Eq[Nat, get(add(n, m), vec_append(n, m, xs, ys), append_right_index(n, m, i)), get(m, ys, i)]:
    return get_append_right(n, m, xs, ys, i)

@theorem
def reversed_lookup(n: Nat, xs: Vec[Nat, n], i: Fin[n]) -> Eq[Nat, get(n, reverse(n, xs), mirror(n, i)), get(n, xs, i)]:
    return reverse_get(n, xs, i)

@dependent
def concrete_fin() -> Eq[Nat, to_nat(2, FS(1, FZ(0))), 1]:
    return refl(1)

@dependent
def concrete_append() -> Eq[Nat, get(2, vec_append(1, 1, VCons(0, 3, VNil()), VCons(0, 4, VNil())), FS(1, FZ(0))), 4]:
    return refl(4)

@dependent
def empty_enumeration() -> Enumeration[Empty]:
    return Enumeration[Empty](Nil[Empty](), MkUnit(), lambda x: absurd(Mem(x, Nil[Empty]()), x))

@dependent
def keep_empty(x: Empty) -> Decidable[Eq[Empty, x, x]]:
    return Yes(refl(x))

@dependent
def all_empty() -> Decidable[Pi[Empty, lambda x: Eq[Empty, x, x]]]:
    return finite_all_decide[Empty, lambda x: Eq[Empty, x, x]](empty_enumeration(), keep_empty)

@dependent
def search_empty() -> Decidable[Sigma[Empty, lambda x: Eq[Empty, x, x]]]:
    return finite_search[Empty, lambda x: Eq[Empty, x, x]](empty_enumeration(), keep_empty)

@dependent
def count_empty() -> Eq[Nat, finite_count[Empty, lambda x: Eq[Empty, x, x]](empty_enumeration(), keep_empty), 0]:
    return refl(0)

@theorem(decreases="x")
def unit_complete(x: Unit) -> Mem(x, Cons(MkUnit(), Nil[Unit]())):
    match x:
        case MkUnit():
            return Left(refl(MkUnit()))

@dependent
def unit_enumeration() -> Enumeration[Unit]:
    return Enumeration[Unit](Cons(MkUnit(), Nil[Unit]()), Pair(lambda impossible: impossible, MkUnit()), lambda x: unit_complete(x))

@dependent
def keep_unit(x: Unit) -> Decidable[Unit]:
    return Yes(MkUnit())

@dependent
def positive_search() -> Eq[Decidable[Sigma[Unit, lambda x: Unit]], finite_search[Unit, lambda x: Unit](unit_enumeration(), keep_unit), Yes[Sigma[Unit, lambda x: Unit]](Pair(MkUnit(), MkUnit()))]:
    return refl(Yes[Sigma[Unit, lambda x: Unit]](Pair(MkUnit(), MkUnit())))

@theorem
def permutation_size(xs: List[Nat], ys: List[Nat], p: Permutation[Nat, xs, ys]) -> Eq[Nat, length(xs), length(ys)]:
    return perm_length(p)

@theorem
def identity_cardinality() -> Eq[Nat, length(bijection_enumeration(identity_bijection[Empty](), empty_enumeration()).elements), length(empty_enumeration().elements)]:
    return bijection_cardinality(identity_bijection[Empty](), empty_enumeration())

@theorem
def identity_is_injective(x: Nat, y: Nat, same: Eq[Nat, identity_bijection[Nat]().forward(x), identity_bijection[Nat]().forward(y)]) -> Eq[Nat, x, y]:
    return bijection_injective(identity_bijection[Nat](), x, y, same)
"#;
    let checked = check_module(source, TARGET).unwrap_or_else(|e| panic!("{e}"));
    assert!(checked.axiom_dependencies.values().all(Vec::is_empty));
    let invalid = format!(
        "{source}\n@theorem\ndef false_permutation() -> Permutation[Nat, Cons(1, Nil[Nat]()), Cons(2, Nil[Nat]())]:\n    return perm_refl(Cons(1, Nil[Nat]()))\n"
    );
    assert!(check_module(&invalid, TARGET).is_err());
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
