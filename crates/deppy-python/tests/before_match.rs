use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, Target};

const FIXTURE: &str = include_str!("../examples/core/before_match.py");
const HEADER: &str = "from deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, Eq, refl, fin0_elim, Sigma, Pair\n";

#[test]
fn locals_are_refined_with_nat_and_vector_scrutinees() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let m = check_module(FIXTURE, target).unwrap();
        let e = m.elaborator;
        let two = E::Zero.succ().succ();
        let value = e.infer(&E::name("count").app(two.clone())).unwrap();
        assert_eq!(
            e.kernel().normalize(&value.term).unwrap(),
            Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
        );
        let proof = e.infer(&E::name("reflexive").app(two.clone())).unwrap();
        let expected = e.infer(&E::refl(two)).unwrap();
        assert_eq!(
            e.kernel().normalize(&proof.term).unwrap(),
            e.kernel().normalize(&expected.term).unwrap()
        );
        let xs = E::vcons(E::Nat, E::Zero, E::Zero.succ(), E::vnil(E::Nat));
        let kept = e
            .infer(&E::name("keep").app(E::Zero.succ()).app(xs.clone()))
            .unwrap();
        let expected = e.infer(&xs).unwrap();
        assert_eq!(
            e.kernel().normalize(&kept.term).unwrap(),
            e.kernel().normalize(&expected.term).unwrap()
        );
    }
}

#[test]
fn locals_before_nested_fin_match_preserve_dependent_types() {
    let source = format!(
        "{HEADER}
@dependent(decreases='xs')
def get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> T:
    evidence: Eq[Fin[n], i, i] = refl(i)
    match xs:
        case VNil():
            return fin0_elim(i)
        case VCons(k, x, rest):
            head = x
            proof: Eq[Fin[S(k)], i, i] = evidence
            match i:
                case FZ(_):
                    return head
                case FS(_, j):
                    return get(k, rest, j)
"
    );
    let m = check_module(&source, Target::Python314).unwrap();
    let e = m.elaborator;
    let xs = E::vcons(
        E::Nat,
        E::Zero.succ(),
        E::Zero,
        E::vcons(E::Nat, E::Zero, E::Zero.succ(), E::vnil(E::Nat)),
    );
    let got = e
        .infer(
            &E::name("get")
                .app(E::Zero.succ().succ())
                .app(xs)
                .app(E::fs(E::Zero.succ(), E::fz(E::Zero))),
        )
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&got.term).unwrap(),
        Term::Succ(Term::Zero.arc()).arc()
    );
}

#[test]
fn fin_match_and_expected_local_sigma_type_are_supported() {
    let source = format!(
        "{HEADER}
@dependent(decreases='i')
def keep(n: Nat, i: Fin[n]) -> Fin[n]:
    pair: Sigma[Nat, lambda k: Fin[k]] = Pair(n, i)
    saved = i
    match i:
        case FZ(k):
            return saved
        case FS(k, j):
            return saved
"
    );
    check_module(&source, Target::Python314).unwrap();
}

#[test]
fn invalid_unused_locals_and_scope_or_descent_violations_are_rejected() {
    for prefix in [
        "unused: Eq[Nat, n, Z()] = refl(n)",
        "unused: Nat = Type",
        "unused = missing",
        "unused = later\n    later = n",
        "n = Z()",
        "unused: Nat",
        "a, b = n",
        "unused = count(n)",
        "unused = n\n    unused = Z()",
    ] {
        let source = format!(
            "{HEADER}
@dependent(decreases='n')
def count(n: Nat) -> Nat:
    {prefix}
    match n:
        case Z():
            return Z()
        case S(k):
            return count(k)
"
        );
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{source}"
        );
    }
    for source in [
        FIXTURE.replace("one = S(Z())", "k = S(Z())"),
        FIXTURE.replace(
            "previous = count(k)",
            "alias = k\n            previous = count(alias)",
        ),
        FIXTURE.replace("match n:", "match one:"),
    ] {
        assert!(
            check_module(&source, Target::Python314).is_err(),
            "{source}"
        );
    }
}

#[test]
fn local_shadowing_does_not_capture_globals_in_signature_or_suffix() {
    let source = format!(
        "{HEADER}
@dependent
def Carrier(n: Nat) -> Type:
    return Nat
@dependent(decreases='n')
def identity(n: Nat, x: Carrier(n)) -> Carrier(n):
    Carrier = Z()
    match n:
        case Z():
            return x
        case S(k):
            return identity(k, x)
"
    );
    let m = check_module(&source, Target::Python314).unwrap();
    let got = m
        .elaborator
        .infer(&E::name("identity").app(E::Zero.succ()).app(E::Zero))
        .unwrap();
    assert_eq!(
        m.elaborator.kernel().normalize(&got.term).unwrap(),
        Term::Zero.arc()
    );
}

#[test]
fn later_patterns_cannot_capture_global_references_in_earlier_locals() {
    let source = format!(
        "{HEADER}
@dependent
def previous(n: Nat) -> Nat:
    return n
@dependent(decreases='n')
def count(n: Nat) -> Nat:
    saved = previous(n)
    match n:
        case Z():
            return saved
        case S(previous):
            return saved
"
    );
    assert!(check_module(&source, Target::Python314).is_err());
}
