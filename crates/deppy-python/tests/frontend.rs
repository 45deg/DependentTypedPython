use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, lower_module, Target};
const HEADER: &str = "from __future__ import annotations\nfrom deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, Eq, refl, Pi, Sigma, Pair\n";
fn source(body: &str) -> String {
    format!("{HEADER}\n{body}")
}
fn accepted(body: &str) -> deppy_python::CheckedModule {
    check_module(&source(body), Target::Python314).unwrap()
}
fn rejected(body: &str) -> deppy_python::Diagnostic {
    check_module(&source(body), Target::Python314)
        .err()
        .expect("must reject")
}
#[test]
fn identity_fixture_checks_and_computes_on_all_targets() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let m = check_module(include_str!("../examples/basics.py"), target).unwrap();
        assert_eq!(m.definitions.len(), 5);
        let e = m.elaborator;
        let result = e.infer(&E::name("identity").app(E::Zero)).unwrap();
        assert_eq!(
            e.kernel().normalize(&result.term).unwrap(),
            Term::Zero.arc()
        );
        let result = e.infer(&E::name("twice").app(E::Zero)).unwrap();
        assert_eq!(
            e.kernel().normalize(&result.term).unwrap(),
            Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
        );
    }
}
#[test]
fn explicit_type_arguments_and_higher_universes() {
    let m = accepted("@dependent\ndef identity[A: Type[1]](x: A) -> A:\n    return x\n@dependent\ndef use(n: Nat) -> Type:\n    return identity[Type](Nat)\n");
    let e = m.elaborator;
    let result = e.infer(&E::name("use").app(E::Zero)).unwrap();
    assert_eq!(e.kernel().normalize(&result.term).unwrap(), Term::Nat.arc());
}
#[test]
fn import_aliases_and_unicode_ranges() {
    let src = "from __future__ import annotations\nfrom deppy import dependent as dep, Nat as 自然数\n@dep\ndef 同一(値: 自然数) -> 自然数:\n    return 値\n";
    let m = check_module(src, Target::Python314).unwrap();
    assert_eq!(m.definitions[0].0, "同一");
    let span = m.definitions[0].2;
    assert!(src[span.start..span.end].contains("def 同一"));
    let bad = src.replace("return 値", "return 未知");
    let error = check_module(&bad, Target::Python314).err().unwrap();
    assert_eq!(&bad[error.span.start..error.span.end], "未知");
}
#[test]
fn sigma_pack_and_dependent_projection() {
    let m = accepted("@dependent\ndef pack[A: Type](n: Nat, xs: Vec[A, n]) -> Sigma[Nat, lambda k: Vec[A, k]]:\n    p: Sigma[Nat, lambda k: Vec[A, k]] = Pair(n, xs)\n    return p\n@dependent\ndef unpack(p: Sigma[Nat, lambda k: Vec[Nat, k]]) -> Vec[Nat, p.fst]:\n    return p.snd\n");
    let e = m.elaborator;
    let packed = E::name("pack").app(E::Zero).app(E::vnil(E::Nat));
    let out = e.infer(&E::name("unpack").app(packed)).unwrap();
    assert_eq!(
        e.kernel().normalize(&out.term).unwrap(),
        Term::VNil(Term::Nat.arc()).arc()
    );
}
#[test]
fn vector_and_finite_constructors() {
    accepted("@dependent\ndef singleton(n: Nat) -> Vec[Nat, S(Z())]:\n    return VCons(Z(), n, VNil())\n@dependent\ndef index(n: Nat) -> Fin[S(S(n))]:\n    return FS(S(n), FZ(n))\n");
    rejected("@dependent\ndef bad(n: Nat) -> Fin[Z()]:\n    return FZ(n)\n");
}
#[test]
fn pi_annotations_and_nat_addition() {
    accepted("@dependent\ndef apply(f: Pi[Nat, lambda n: Nat], n: Nat) -> Nat:\n    return f(n)\n@dependent\ndef step(n: Nat) -> Eq[Nat, 1 + n, S(n)]:\n    return refl(S(n))\n");
    rejected("@dependent\ndef wrong(n: Nat) -> Eq[Nat, n + 0, n]:\n    return refl(n)\n");
}
#[test]
fn annotations_are_required_and_never_executed() {
    for body in [
        "@dependent\ndef f(n) -> Nat:\n    return n",
        "@dependent\ndef f(n: Nat):\n    return n",
        "@dependent\ndef f(n: __import__('os').system('false')) -> Nat:\n    return n",
        "@dependent\ndef f[A](n: A) -> A:\n    return n",
    ] {
        rejected(body);
    }
}
#[test]
fn future_import_and_static_import_rules() {
    assert!(check_module(
        "from deppy import dependent, Nat\n@dependent\ndef f(n: Nat) -> Nat:\n    return n",
        Target::Python314
    )
    .is_err());
    for src in [
        "from deppy import *",
        "from os import system",
        "from .deppy import Nat",
        "from deppy import Nat\nfrom __future__ import annotations",
        "from deppy import Nat as N, Type as N",
    ] {
        assert!(lower_module(src, Target::Python314).is_err());
    }
}
#[test]
fn reassignment_effects_and_control_flow_are_rejected() {
    for body in [
        "n = Z()\n    return n",
        "x = n\n    x = S(x)\n    return x",
        "print(n)\n    return n",
        "while True:\n        pass\n    return n",
        "return n\n    x = n",
        "match n:\n        case Z():\n            return n",
        "n.attr = n\n    return n",
        "a = b = n\n    return n",
    ] {
        rejected(&format!("@dependent\ndef f(n: Nat) -> Nat:\n    {body}"));
    }
}
#[test]
fn forward_self_and_unchecked_calls_are_rejected() {
    for body in ["@dependent\ndef f(n: Nat) -> Nat:\n    return f(n)", "@dependent\ndef f(n: Nat) -> Nat:\n    return later(n)\n@dependent\ndef later(n: Nat) -> Nat:\n    return n", "def ordinary(n):\n    return n\n@dependent\ndef f(n: Nat) -> Nat:\n    return ordinary(n)"] { rejected(body); }
}
#[test]
fn module_binding_collisions_are_rejected() {
    for body in [
        "@dependent\ndef Nat(n: Nat) -> Nat:\n    return n",
        "@dependent\ndef f(n: Nat) -> Nat:\n    return n\ndef f(n):\n    return n",
        "Nat = 0",
        "from deppy import Nat",
        "@dependent\ndef f(n: Nat, n: Nat) -> Nat:\n    return n",
    ] {
        rejected(body);
    }
}
#[test]
fn local_scope_blocks_global_or_import_use_before_assignment() {
    let err = rejected(
        "@dependent\ndef f(n: Nat) -> Nat:\n    value = S(n)\n    S = n\n    return value",
    );
    assert!(err.message.contains("before"));
    accepted("@dependent\ndef f(S: Nat) -> Nat:\n    return S\n@dependent\ndef g(n: Nat) -> Nat:\n    S = n\n    return S");
}
#[test]
fn invalid_or_unsupported_function_signatures() {
    for signature in ["n: Nat = Z()", "*n: Nat", "*, n: Nat", "**n: Nat"] {
        rejected(&format!(
            "@dependent\ndef f({signature}) -> Nat:\n    return n"
        ));
    }
    rejected("@dependent(decreases='missing')\ndef f(n: Nat) -> Nat:\n    return n");
    rejected("@dependent\nasync def f(n: Nat) -> Nat:\n    return n");
    rejected("@dependent\ndef f(n: Nat) -> Nat:\n    return f(n=n)");
}
#[test]
fn parser_errors_and_version_errors_have_ranges() {
    let bad = source("@dependent\ndef f(:\n    return Z()");
    let error = lower_module(&bad, Target::Python314).unwrap_err();
    assert!(error.span.start <= error.span.end && error.span.end <= bad.len());
    let versioned = source("@dependent\ndef f[A: Type = Nat](n: A) -> A:\n    return n");
    let error = lower_module(&versioned, Target::Python312).unwrap_err();
    assert!(error.message.contains("target-version"));
    assert!(lower_module(&versioned, Target::Python313)
        .unwrap_err()
        .message
        .contains("default type"));
}
#[test]
fn python314_template_strings_parse_but_are_outside_dependent_subset() {
    let src = source("@dependent\ndef f(n: Nat) -> Nat:\n    return t'{n}'");
    assert!(lower_module(&src, Target::Python313)
        .unwrap_err()
        .message
        .contains("target-version"));
    assert!(lower_module(&src, Target::Python314)
        .unwrap_err()
        .message
        .contains("unsupported dependent expression"));
}
#[test]
fn ordinary_python_assertions_are_not_treated_as_proofs() {
    let module = accepted("def ordinary():\n    raise RuntimeError('not executed')\nassert ordinary()\n@dependent\ndef f(n: Nat) -> Nat:\n    return n");
    assert_eq!(module.definitions.len(), 1);
}
#[test]
fn errors_in_discarded_values_and_non_cumulative_universes() {
    rejected("@dependent\ndef f(n: Nat) -> Nat:\n    unused: Nat = Type\n    return n");
    rejected("@dependent\ndef f(n: Nat) -> Type:\n    return Type");
    rejected("@dependent\ndef f(n: Nat) -> Nat:\n    return True");
    rejected("@dependent\ndef f(n: Nat) -> Nat:\n    return 1000000");
    rejected("@dependent\ndef f(n: Nat) -> Type[4294967296]:\n    return Nat");
}

#[test]
fn zero_parameter_constants_and_empty_call_validation() {
    accepted("@dependent\ndef zero() -> Nat:\n    return Z()\n@dependent\ndef use(n: Nat) -> Nat:\n    return zero()");
    rejected("@dependent\ndef identity(n: Nat) -> Nat:\n    return n\n@dependent\ndef bad(n: Nat) -> Nat:\n    return identity()");
}

#[test]
fn structural_python_fixture_checks_and_computes() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let module = check_module(include_str!("../examples/structural.py"), target).unwrap();
        let e = module.elaborator;
        for n in 0..4 {
            for m in 0..4 {
                let nat = |n| (0..n).fold(E::Zero, |n, _| n.succ());
                let result = e.infer(&E::name("add").app(nat(n)).app(nat(m))).unwrap();
                let expected = e.infer(&nat(n + m)).unwrap();
                assert_eq!(e.kernel().normalize(&result.term).unwrap(), expected.term);
            }
        }
        let nil = E::vnil(E::Nat);
        let one = E::vcons(E::Nat, E::Zero, E::Zero.succ(), nil.clone());
        let result = e
            .infer(
                &E::name("append")
                    .app(E::Zero.succ())
                    .app(E::Zero.succ())
                    .app(one.clone())
                    .app(one.clone()),
            )
            .unwrap();
        let expected = e
            .infer(&E::vcons(E::Nat, E::Zero.succ(), E::Zero.succ(), one))
            .unwrap();
        assert_eq!(
            e.kernel().normalize(&result.term).unwrap(),
            e.kernel().normalize(&expected.term).unwrap()
        );
    }
}

#[test]
fn structural_recursion_and_coverage_are_checked() {
    let fixture = include_str!("../examples/structural.py");
    for bad in [
        fixture.replace("add(k, m)", "add(n, m)"),
        fixture.replace("add(k, m)", "add(S(k), m)"),
        fixture.replace("add(k, m)", "add(k)"),
        fixture.replace("append(k, m, rest, ys)", "append(n, m, rest, ys)"),
        fixture.replace("append(k, m, rest, ys)", "append(k, m, xs, ys)"),
        fixture.replace("case S(k):", "case Z():"),
        fixture.replace("        case S(k):\n            return S(add(k, m))", ""),
        fixture.replace("case Z():", "case Z() if True:"),
        fixture.replace("case S(k):", "case S(S(k)):"),
        fixture.replace("case S(k):", "case S(_):"),
        fixture.replace("case S(k):", "case S(n):"),
    ] {
        assert!(check_module(&bad, Target::Python314).is_err(), "{bad}");
    }
}

#[test]
fn structural_aliases_globals_and_local_scope() {
    accepted("@dependent\ndef step(n: Nat) -> Nat:\n    return S(n)\n@dependent(decreases='n')\ndef count(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return Z()\n        case S(k):\n            return step(count(k))");
    let fixture = include_str!("../examples/structural.py")
        .replace("Nat, Z, S", "Nat, Z as Zero, S as Succ")
        .replace("Z()", "Zero()")
        .replace("S(", "Succ(");
    check_module(&fixture, Target::Python314).unwrap();
    // Pattern captures, like assignments, make names local throughout the function.
    rejected("@dependent(decreases='n')\ndef count(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return S(Z())\n        case S(S):\n            return Z()");
    rejected("@dependent(decreases='n')\ndef count(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return k\n        case S(k):\n            return k");
    rejected("@dependent(decreases='n')\ndef count(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return Z()\n        case S(k):\n            alias = k\n            return count(alias)");
}

#[test]
fn structural_fin_matches_compute() {
    let m = accepted("@dependent(decreases='i')\ndef rank(n: Nat, i: Fin[n]) -> Nat:\n    match i:\n        case FZ(k):\n            return Z()\n        case FS(k, j):\n            return S(rank(k, j))");
    let e = m.elaborator;
    let result = e
        .infer(
            &E::name("rank")
                .app(E::Zero.succ().succ())
                .app(E::fs(E::Zero.succ(), E::fz(E::Zero))),
        )
        .unwrap();
    assert_eq!(
        e.kernel().normalize(&result.term).unwrap(),
        Term::Succ(Term::Zero.arc()).arc()
    );
}

#[test]
fn python_get_and_zero_right_compute() {
    for target in [Target::Python312, Target::Python313, Target::Python314] {
        let m = check_module(include_str!("../examples/proofs.py"), target).unwrap();
        let e = m.elaborator;
        let nat = |n| (0..n).fold(E::Zero, |n, _| n.succ());
        for len in 1..5 {
            let xs = (0..len).rev().fold(E::vnil(E::Nat), |xs, i| {
                E::vcons(E::Nat, nat(len - i - 1), nat(i), xs)
            });
            for index in 0..len {
                let i = (0..index).fold(E::fz(nat(len - index - 1)), |i, j| {
                    E::fs(nat(len - index + j), i)
                });
                let got = e
                    .infer(&E::name("get").app(nat(len)).app(xs.clone()).app(i))
                    .unwrap();
                let want = e.infer(&nat(index)).unwrap();
                assert_eq!(e.kernel().normalize(&got.term).unwrap(), want.term);
            }
        }
        for n in 0..5 {
            let got = e.infer(&E::name("zero_right").app(nat(n))).unwrap();
            let want = e.infer(&nat(n).refl()).unwrap();
            assert_eq!(e.kernel().normalize(&got.term).unwrap(), want.term);
        }
    }
}

#[test]
fn python_proof_operations_reject_invalid_evidence() {
    let fixture = include_str!("../examples/proofs.py");
    for bad in [
        fixture.replace("fin0_elim(i)", "fin0_elim(Z())"),
        fixture.replace("cong(S, zero_right(k))", "refl(n)"),
        fixture.replace("cong(S, zero_right(k))", "cong(Z(), zero_right(k))"),
        fixture.replace("get(k, rest, j)", "get(k, rest, i)"),
        fixture.replace("case FS(_, j):", "case FS(_, _):"),
    ] {
        assert!(check_module(&bad, Target::Python314).is_err(), "{bad}");
    }
    let aliased = fixture
        .replace("FS, fin0_elim", "FS, fin0_elim as absurd")
        .replace("Eq, refl, cong", "Eq, refl, cong as congruence")
        .replace("fin0_elim(i)", "absurd(i)")
        .replace("cong(S,", "congruence(S,");
    check_module(&aliased, Target::Python314).unwrap();
}

#[test]
fn recursive_branch_lets_keep_expected_types_and_compute() {
    let fixture = include_str!("../examples/proofs.py")
        .replace("return cong(S, zero_right(k))", "ih: Eq[Nat, k + 0, k] = zero_right(k)\n            result = cong(S, ih)\n            return result")
        .replace("return get(k, rest, j)", "value: T = get(k, rest, j)\n                    return value");
    let module = check_module(&fixture, Target::Python314).unwrap();
    let e = module.elaborator;
    let out = e
        .infer(&E::name("zero_right").app(E::Zero.succ().succ()))
        .unwrap();
    let expected = e.infer(&E::Zero.succ().succ().refl()).unwrap();
    assert_eq!(e.kernel().normalize(&out.term).unwrap(), expected.term);
    accepted("@dependent(decreases='n')\ndef pair(n: Nat) -> Sigma[Nat, lambda k: Nat]:\n    match n:\n        case Z():\n            x = Z()\n            return Pair(x, x)\n        case S(k):\n            p = pair(k)\n            return Pair(S(p.fst), p.snd)");
}

#[test]
fn recursive_branch_lets_reject_scope_errors_and_invalid_unused_values() {
    let base = "@dependent(decreases='n')\ndef f(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return Z()\n        case S(k):\n            BODY";
    for body in [
        "alias = k\n            return f(alias)",
        "k = Z()\n            return f(k)",
        "unused: Nat = Nat\n            return k",
        "x = x\n            return x",
        "x = S(k)\n            S = k\n            return x",
        "x = k\n            x = Z()\n            return x",
        "x: Nat\n            return k",
        "x, y = k\n            return k",
    ] {
        rejected(&base.replace("BODY", body));
    }
    rejected(
        &base
            .replace("return Z()", "return x")
            .replace("BODY", "x = k\n            return x"),
    );
}
