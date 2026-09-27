use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, Target};
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, record, Type, Nat, Z, S, Vec, VNil, Sigma, Pair\n";
fn check(body: &str) -> deppy_python::CheckedModule {
    check_module(&format!("{HEADER}{body}"), Target::Python314).unwrap()
}
fn reject(body: &str) {
    assert!(
        check_module(&format!("{HEADER}{body}"), Target::Python314).is_err(),
        "{body}"
    );
}
#[test]
fn dependent_record_round_trip_computes() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let m = check_module(include_str!("../examples/core/records.py"), target).unwrap();
        assert_eq!(m.definitions.len(), 4);
        let e = m.elaborator;
        let xs = E::vcons(E::Nat, E::Zero, E::Zero.succ(), E::vnil(E::Nat));
        let pair = E::name("pack").app(E::Zero.succ()).app(xs.clone());
        let round_trip = E::name("as_pair").app(E::name("as_record").app(pair));
        let len = e.infer(&round_trip.clone().fst()).unwrap();
        assert_eq!(
            e.kernel().normalize(&len.term).unwrap(),
            Term::Succ(Term::Zero.arc()).arc()
        );
        let values = e.infer(&round_trip.snd()).unwrap();
        let expected = e.infer(&xs).unwrap();
        assert_eq!(
            e.kernel().normalize(&values.term).unwrap(),
            e.kernel().normalize(&expected.term).unwrap()
        );
    }
}
#[test]
fn record_constructors_infer_or_accept_explicit_parameters() {
    let m = check("@record\nclass Box[T: Type]:\n    value: T\n@dependent\ndef make(n: Nat) -> Box[Nat]:\n    return Box[Nat](n)\n@dependent\ndef get(n: Nat) -> Nat:\n    box = make(n)\n    return box.value\n");
    let e = m.elaborator;
    let got = e.infer(&E::name("get").app(E::Zero.succ())).unwrap();
    assert_eq!(
        e.kernel().normalize(&got.term).unwrap(),
        Term::Succ(Term::Zero.arc()).arc()
    );
    check("@record\nclass Unit[T: Type]:\n    pass\n@dependent\ndef make(n: Nat) -> Unit[Nat]:\n    return Unit()\n");
    check("@record\nclass Empty:\n    pass\n@dependent\ndef make(n: Nat) -> Empty:\n    return Empty()\n");
    let fixture = include_str!("../examples/core/records.py")
        .replace("record,", "record as rec,")
        .replace("@record", "@rec");
    check_module(&fixture, Target::Python314).unwrap();
}
#[test]
fn record_nominality_and_dependent_fields_are_checked() {
    reject("@record\nclass A:\n    x: Nat\n@record\nclass B:\n    y: Nat\n@dependent\ndef bad(n: Nat) -> A:\n    return B(n)");
    let fixture = include_str!("../examples/core/records.py");
    for bad in [
        fixture
            .replace("SomeVec(p.fst, p.snd)", "SomeVec(S(p.fst), p.snd)")
            .replace("Nat,", "Nat, S,"),
        fixture.replace("SomeVec(p.fst, p.snd)", "p"),
        fixture.replace("r.value", "r.missing"),
        fixture.replace("self.n", "self.value"),
        fixture.replace("self.n", "self.missing"),
    ] {
        assert!(check_module(&bad, Target::Python314).is_err(), "{bad}");
    }
    reject("@record\nclass Box:\n    item: Nat\n@dependent\ndef bad(n: Nat) -> Nat:\n    return n.item");
}
#[test]
fn record_declarations_reject_unsupported_or_ill_scoped_forms() {
    for body in [
        "@record\nclass R:\n    x: R",
        "@record\nclass R:\n    x: Later\n@record\nclass Later:\n    pass",
        "@record\nclass R:\n    x: Nat\n    x: Nat",
        "@record\nclass R[T: Type]:\n    T: Nat",
        "@record\nclass R[self: Type]:\n    pass",
        "@record\nclass R:\n    fst: Nat",
        "@record\nclass R:\n    x: Nat = Z()",
        "@record\nclass R:\n    def method(self):\n        return 0",
        "@record\nclass R(Nat):\n    pass",
        "@record\nclass R(metaclass=Nat):\n    pass",
        "@record()\nclass R:\n    pass",
        "@record\nclass R[T]:\n    pass",
        "@record\nclass R[T: Type = Nat]:\n    pass",
        "@record\nclass R:\n    carrier: Type",
        "@record\nclass R:\n    x: Nat\n@dependent\ndef bad(n: Nat) -> R:\n    return R()",
        "@record\nclass R:\n    x: Nat\n@dependent\ndef bad(n: Nat) -> R:\n    return R(x=n)",
        "@record\nclass R:\n    x: Nat\n@dependent\ndef bad(n: Nat) -> R:\n    return R[Nat](n)",
        "@record\nclass R:\n    x: Nat\n@dependent\ndef bad(n: Nat) -> R:\n    value = R(n)\n    R = n\n    return value",
    ] { reject(body); }
}
#[test]
fn shared_field_names_are_selected_from_receiver_types() {
    check("@record\nclass A:\n    x: Nat\n@record\nclass B:\n    x: Nat\n@dependent\ndef read(a: A) -> Nat:\n    return a.x");
}
#[test]
fn records_work_in_structural_functions_and_later_field_types() {
    let m = check("@record\nclass Box:\n    item: Nat\n@dependent(decreases='n')\ndef build(n: Nat) -> Box:\n    match n:\n        case Z():\n            return Box(Z())\n        case S(k):\n            return Box(S(build(k).item))\n@dependent\ndef read(n: Nat) -> Nat:\n    return build(n).item");
    let e = m.elaborator;
    let got = e
        .infer(&E::name("read").app(E::Zero.succ().succ()))
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&got.term).unwrap(),
        Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
    );
    check("@record\nclass Inner:\n    size: Nat\n@record\nclass Outer:\n    inner: Inner\n    values: Vec[Nat, self.inner.size]");
}

#[test]
fn record_field_references_do_not_capture_lambda_or_global_names() {
    check("@record\nclass R:\n    new: Nat\n@dependent\ndef read(n: Nat) -> Nat:\n    return R(n).new");
    // The second field is a function returning evidence about the stored n,
    // even when its lambda parameter happens to have the same source name.
    let source = "from __future__ import annotations\nfrom deppy import record, dependent, Nat, Eq, Pi, Z, refl\n@record\nclass R:\n    n: Nat\n    proof: Pi[Nat, lambda n: Eq[Nat, self.n, self.n]]\n@dependent\ndef proof(n: Nat) -> Eq[Nat, Z(), Z()]:\n    return refl(Z())\n@dependent\ndef make(n: Nat) -> R:\n    return R(Z(), proof)\n";
    check_module(source, Target::Python314).unwrap();
    let globals = "from __future__ import annotations\nfrom deppy import record, dependent, Nat\n@dependent\ndef value(n: Nat) -> Nat:\n    return n\n@record\nclass R:\n    value: Nat\n    other: Nat\n";
    check_module(globals, Target::Python314).unwrap();
    // A field called Nat must not capture the imported Nat used by the next field.
    check("@record\nclass R:\n    Nat: Nat\n    other: Nat\n@dependent\ndef make(n: Nat) -> R:\n    return R(n, n)");
}

#[test]
fn shared_field_names_support_chains_lets_and_dependent_results() {
    let m = check_module(
        include_str!("../examples/core/branch_fields.py"),
        Target::Python314,
    )
    .unwrap();
    let got = m
        .elaborator
        .infer(&E::name("count").app(E::Zero.succ().succ()))
        .unwrap();
    assert_eq!(
        m.elaborator.kernel().normalize(&got.term).unwrap(),
        Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
    );
    let source = "@record\nclass A:\n    value: Nat\n@record\nclass B:\n    ignored: Nat\n    value: A\n@record\nclass C[T: Type]:\n    n: Nat\n    value: Vec[T, self.n]\n@dependent\ndef read(n: Nat) -> Nat:\n    box = B(Z(), A(n))\n    return box.value.value\n@dependent\ndef values[T: Type](c: C[T]) -> Vec[T, c.n]:\n    return c.value";
    let m = check(source);
    let got = m
        .elaborator
        .infer(&E::name("read").app(E::Zero.succ()))
        .unwrap();
    assert_eq!(
        m.elaborator.kernel().normalize(&got.term).unwrap(),
        Term::Succ(Term::Zero.arc()).arc()
    );
    reject(&source.replace("return box.value.value", "return box.value"));
    reject(&source.replace("return c.value", "return c.ignored"));
    check("@record\nclass A:\n    value: Nat\n@record\nclass B:\n    value: Nat\n@dependent(decreases='n')\ndef read(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return A(Z()).value\n        case S(k):\n            box = B(read(k))\n            return S(box.value)");
}
