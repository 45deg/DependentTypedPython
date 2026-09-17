use deppy_core::{Error, Kernel, Relevance::Runtime, Term, Tm};
fn nat() -> Tm {
    Term::Nat.arc()
}
fn zero() -> Tm {
    Term::Zero.arc()
}
fn succ(n: Tm) -> Tm {
    Term::Succ(n).arc()
}
fn lam(domain: Tm, body: Tm) -> Tm {
    Term::Lam {
        relevance: Runtime,
        domain,
        body,
    }
    .arc()
}

#[test]
fn nat_is_small_and_constructors_inhabit_nat() {
    let k = Kernel::default();
    assert_eq!(k.infer(&nat()).unwrap(), Term::Universe(0).arc());
    for n in [zero(), succ(zero()), succ(succ(zero()))] {
        assert_eq!(k.infer(&n).unwrap(), nat());
        assert_eq!(k.normalize(&n).unwrap(), n);
    }
}
#[test]
fn constructor_equality_is_structural() {
    let k = Kernel::default();
    assert!(k.equivalent(&succ(zero()), &succ(zero()), &nat()).unwrap());
    assert!(!k.equivalent(&zero(), &succ(zero()), &nat()).unwrap());
    assert!(!k
        .equivalent(&succ(zero()), &succ(succ(zero())), &nat())
        .unwrap());
}
#[test]
fn successor_reduces_its_argument_and_preserves_neutrals() {
    let k = Kernel::default();
    let f = lam(nat(), succ(Term::Var(0).arc()));
    assert_eq!(k.normalize(&f).unwrap(), f);
    let app = Term::App {
        function: lam(nat(), Term::Var(0).arc()),
        argument: zero(),
    }
    .arc();
    assert_eq!(k.normalize(&succ(app)).unwrap(), succ(zero()));
}
#[test]
fn rejects_non_nat_successor_and_nat_as_a_value() {
    let k = Kernel::default();
    for bad in [nat(), Term::Universe(0).arc(), lam(nat(), zero())] {
        assert!(matches!(
            k.infer(&succ(bad)),
            Err(Error::TypeMismatch { .. })
        ));
    }
    assert!(k.check(&nat(), &nat()).is_err());
    assert!(k.check(&zero(), &Term::Universe(0).arc()).is_err());
}
#[test]
fn rejects_nat_value_in_type_position() {
    assert_eq!(
        Kernel::default().infer(&lam(zero(), zero())),
        Err(Error::ExpectedUniverse)
    );
}
#[test]
fn nat_still_obeys_non_cumulative_universes_and_budget() {
    assert!(Kernel::default()
        .check(&nat(), &Term::Universe(1).arc())
        .is_err());
    assert_eq!(
        Kernel::new(1).normalize(&succ(zero())),
        Err(Error::BudgetExceeded)
    );
}
