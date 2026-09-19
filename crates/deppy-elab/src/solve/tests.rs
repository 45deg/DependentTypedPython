use super::*;
fn u(n: u32) -> T {
    Term::Universe(n).arc()
}
fn local(id: Id) -> T {
    Term::Local(id).arc()
}

fn inductive_children(child: T) -> Vec<T> {
    let n = Term::Nat.arc();
    vec![
        Term::Inductive {
            id: 1,
            parameters: vec![child.clone()],
        }
        .arc(),
        Term::Constructor {
            id: 1,
            parameters: vec![child.clone()],
            fields: vec![],
        }
        .arc(),
        Term::Constructor {
            id: 1,
            parameters: vec![],
            fields: vec![child.clone()],
        }
        .arc(),
        Term::Elim {
            id: 1,
            parameters: vec![child.clone()],
            level: 0,
            motive: n.clone(),
            branch: n.clone(),
            scrutinee: n.clone(),
        }
        .arc(),
        Term::Elim {
            id: 1,
            parameters: vec![],
            level: 0,
            motive: child.clone(),
            branch: n.clone(),
            scrutinee: n.clone(),
        }
        .arc(),
        Term::Elim {
            id: 1,
            parameters: vec![],
            level: 0,
            motive: n.clone(),
            branch: child.clone(),
            scrutinee: n.clone(),
        }
        .arc(),
        Term::Elim {
            id: 1,
            parameters: vec![],
            level: 0,
            motive: n.clone(),
            branch: n.clone(),
            scrutinee: child,
        }
        .arc(),
    ]
}
#[test]
fn inductive_children_enforce_occurs_scope_and_substitution() {
    let mut s = State::new(100_000);
    let m = s.meta(&vec![], u(0));
    for term in inductive_children(m) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::new()),
            Err(Error::OccursCheck)
        );
    }
    for term in inductive_children(local(100)) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::new()),
            Err(Error::ScopeEscape)
        );
        let closed = s
            .subst(&term, &HashMap::from([(100, Term::Nat.arc())]))
            .unwrap();
        s.validate_solution(0, &closed, &mut HashSet::new())
            .unwrap();
    }
}
#[test]
fn kernel_rechecks_embedded_constructor_before_elimination() {
    let mut k = Kernel::default();
    k.declare(
        1,
        deppy_core::InductiveDecl {
            parameters: vec![],
            fields: vec![Core::Nat.arc()],
            level: 0,
        },
    )
    .unwrap();
    let mut s = State::with_kernel(100_000, k.clone());
    let motive = Term::Lam {
        id: 0,
        plicity: Plicity::Explicit,
        domain: Term::Inductive {
            id: 1,
            parameters: vec![],
        }
        .arc(),
        body: Term::Nat.arc(),
    }
    .arc();
    let branch = Term::Lam {
        id: 1,
        plicity: Plicity::Explicit,
        domain: Term::Nat.arc(),
        body: Term::Zero.arc(),
    }
    .arc();
    let bad = Term::Elim {
        id: 1,
        parameters: vec![],
        level: 0,
        motive,
        branch,
        scrutinee: Term::Constructor {
            id: 1,
            parameters: vec![],
            fields: vec![u(0)],
        }
        .arc(),
    }
    .arc();
    assert!(matches!(
        s.finish(bad, Term::Nat.arc(), &k),
        Err(Error::Kernel(_))
    ));
}

fn sigma_children(child: T) -> Vec<T> {
    let n = Term::Nat.arc();
    vec![
        Term::Sigma {
            id: 50,
            domain: child.clone(),
            body: n.clone(),
        }
        .arc(),
        Term::Sigma {
            id: 50,
            domain: n.clone(),
            body: child.clone(),
        }
        .arc(),
        Term::Pair {
            ty: child.clone(),
            fst: n.clone(),
            snd: n.clone(),
        }
        .arc(),
        Term::Pair {
            ty: n.clone(),
            fst: child.clone(),
            snd: n.clone(),
        }
        .arc(),
        Term::Pair {
            ty: n.clone(),
            fst: n.clone(),
            snd: child.clone(),
        }
        .arc(),
        Term::Fst(child.clone()).arc(),
        Term::Snd(child).arc(),
    ]
}
#[test]
fn sigma_children_enforce_occurs_and_scope_checks() {
    let mut s = State::new(100_000);
    let m = s.meta(&vec![], u(0));
    for term in sigma_children(m) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::new()),
            Err(Error::OccursCheck)
        );
    }
    for term in sigma_children(local(100)) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::new()),
            Err(Error::ScopeEscape)
        );
    }
    let bound = Term::Sigma {
        id: 50,
        domain: u(0),
        body: local(50),
    }
    .arc();
    s.validate_solution(0, &bound, &mut HashSet::new()).unwrap();
    let substituted = s.subst(&bound, &HashMap::from([(50, local(100))])).unwrap();
    s.validate_solution(0, &substituted, &mut HashSet::new())
        .unwrap();
}
#[test]
fn kernel_rechecks_pairs_before_projection_discards_components() {
    for first in [true, false] {
        let mut s = State::new(100_000);
        let ty = Term::Sigma {
            id: 0,
            domain: Term::Nat.arc(),
            body: Term::Nat.arc(),
        }
        .arc();
        let p = Term::Pair {
            ty,
            fst: if first { Term::Zero.arc() } else { u(0) },
            snd: if first { u(0) } else { Term::Zero.arc() },
        }
        .arc();
        let projection = if first { Term::Fst(p) } else { Term::Snd(p) }.arc();
        assert!(matches!(
            s.finish(projection, Term::Nat.arc(), &Kernel::default()),
            Err(Error::Kernel(_))
        ));
    }
}

fn indexed_children(child: T) -> Vec<T> {
    vec![
        Term::Vec {
            ty: child.clone(),
            len: local(0),
        }
        .arc(),
        Term::Vec {
            ty: local(0),
            len: child.clone(),
        }
        .arc(),
        Term::VNil { ty: child.clone() }.arc(),
        Term::VCons {
            ty: child.clone(),
            len: local(0),
            head: local(0),
            tail: local(0),
        }
        .arc(),
        Term::VCons {
            ty: local(0),
            len: child.clone(),
            head: local(0),
            tail: local(0),
        }
        .arc(),
        Term::VCons {
            ty: local(0),
            len: local(0),
            head: child.clone(),
            tail: local(0),
        }
        .arc(),
        Term::VCons {
            ty: local(0),
            len: local(0),
            head: local(0),
            tail: child.clone(),
        }
        .arc(),
        Term::Fin {
            bound: child.clone(),
        }
        .arc(),
        Term::FZ {
            bound: child.clone(),
        }
        .arc(),
        Term::FS {
            bound: child.clone(),
            pred: local(0),
        }
        .arc(),
        Term::FS {
            bound: local(0),
            pred: child.clone(),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: child.clone(),
            motive: local(0),
            nil: local(0),
            cons: local(0),
            len: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: local(0),
            motive: child.clone(),
            nil: local(0),
            cons: local(0),
            len: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: local(0),
            motive: local(0),
            nil: child.clone(),
            cons: local(0),
            len: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: local(0),
            motive: local(0),
            nil: local(0),
            cons: child.clone(),
            len: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: local(0),
            motive: local(0),
            nil: local(0),
            cons: local(0),
            len: child.clone(),
            scrutinee: local(0),
        }
        .arc(),
        Term::VecElim {
            level: 0,
            ty: local(0),
            motive: local(0),
            nil: local(0),
            cons: local(0),
            len: local(0),
            scrutinee: child.clone(),
        }
        .arc(),
        Term::FinElim {
            level: 0,
            motive: child.clone(),
            zero: local(0),
            step: local(0),
            bound: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::FinElim {
            level: 0,
            motive: local(0),
            zero: child.clone(),
            step: local(0),
            bound: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::FinElim {
            level: 0,
            motive: local(0),
            zero: local(0),
            step: child.clone(),
            bound: local(0),
            scrutinee: local(0),
        }
        .arc(),
        Term::FinElim {
            level: 0,
            motive: local(0),
            zero: local(0),
            step: local(0),
            bound: child.clone(),
            scrutinee: local(0),
        }
        .arc(),
        Term::FinElim {
            level: 0,
            motive: local(0),
            zero: local(0),
            step: local(0),
            bound: local(0),
            scrutinee: child.clone(),
        }
        .arc(),
        Term::Fin0Elim {
            ty: child.clone(),
            absurd: local(0),
        }
        .arc(),
        Term::Fin0Elim {
            ty: local(0),
            absurd: child.clone(),
        }
        .arc(),
    ]
}
#[test]
fn indexed_children_enforce_occurs_and_scope_checks() {
    let mut s = State::new(100_000);
    let m = s.meta(&vec![], u(0));
    for term in indexed_children(m) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::from([0])),
            Err(Error::OccursCheck)
        );
    }
    for term in indexed_children(local(100)) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::from([0])),
            Err(Error::ScopeEscape)
        );
    }
}
#[test]
fn kernel_rechecks_indexed_eliminators_before_discarding_branches() {
    let mut s = State::new(10_000);
    let bad_vec = Term::VecElim {
        level: 0,
        ty: Term::Nat.arc(),
        motive: Term::Nat.arc(),
        nil: Term::Zero.arc(),
        cons: Term::Zero.arc(),
        len: Term::Zero.arc(),
        scrutinee: Term::VNil {
            ty: Term::Nat.arc(),
        }
        .arc(),
    }
    .arc();
    assert!(matches!(
        s.finish(bad_vec, Term::Nat.arc(), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
    let id = s.fresh();
    let zero = Term::Lam {
        id,
        plicity: Plicity::Explicit,
        domain: Term::Nat.arc(),
        body: Term::Zero.arc(),
    }
    .arc();
    let bad_fin = Term::FinElim {
        level: 0,
        motive: Term::Nat.arc(),
        zero,
        step: Term::Zero.arc(),
        bound: Term::Succ(Term::Zero.arc()).arc(),
        scrutinee: Term::FZ {
            bound: Term::Zero.arc(),
        }
        .arc(),
    }
    .arc();
    assert!(matches!(
        s.finish(bad_fin, Term::Nat.arc(), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
}
fn equality_children(child: T) -> Vec<T> {
    let mut terms = vec![
        Term::Eq {
            ty: child.clone(),
            left: local(0),
            right: local(0),
        }
        .arc(),
        Term::Eq {
            ty: u(0),
            left: child.clone(),
            right: local(0),
        }
        .arc(),
        Term::Eq {
            ty: u(0),
            left: local(0),
            right: child.clone(),
        }
        .arc(),
        Term::Refl {
            ty: child.clone(),
            value: local(0),
        }
        .arc(),
        Term::Refl {
            ty: u(0),
            value: child.clone(),
        }
        .arc(),
    ];
    for index in 0..6 {
        let mut fields = [u(0), local(0), local(0), local(0), local(0), local(0)];
        fields[index] = child.clone();
        let [ty, left, motive, base, right, proof] = fields;
        terms.push(
            Term::J {
                level: 0,
                ty,
                left,
                motive,
                base,
                right,
                proof,
            }
            .arc(),
        );
    }
    terms
}
#[test]
fn equality_children_enforce_occurs_and_scope_checks() {
    let mut s = State::new(100_000);
    let m = s.meta(&vec![], u(0));
    for term in equality_children(m) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::from([0])),
            Err(Error::OccursCheck)
        );
    }
    for term in equality_children(local(100)) {
        assert_eq!(
            s.validate_solution(0, &term, &mut HashSet::from([0])),
            Err(Error::ScopeEscape)
        );
    }
}
#[test]
fn kernel_sees_invalid_j_before_iota_reduction() {
    let mut s = State::new(10_000);
    let invalid = Term::J {
        level: 0,
        ty: Term::Nat.arc(),
        left: Term::Zero.arc(),
        motive: Term::Nat.arc(),
        base: Term::Zero.arc(),
        right: Term::Zero.arc(),
        proof: Term::Refl {
            ty: Term::Nat.arc(),
            value: Term::Zero.arc(),
        }
        .arc(),
    }
    .arc();
    assert!(matches!(
        s.finish(invalid, Term::Nat.arc(), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
}

#[test]
fn rejects_direct_occurs_cycle() {
    let mut s = State::new(10_000);
    let m = s.meta(&vec![], u(1));
    let rhs = Term::App(m.clone(), u(0)).arc();
    assert_eq!(s.unify(&m, &rhs), Err(Error::OccursCheck));
}
#[test]
fn rejects_indirect_occurs_cycle() {
    let mut s = State::new(10_000);
    let a = s.meta(&vec![], u(1));
    let b = s.meta(&vec![], u(1));
    s.unify(&a, &b).unwrap();
    assert_eq!(
        s.unify(&b, &Term::App(a, u(0)).arc()),
        Err(Error::OccursCheck)
    );
}
#[test]
fn rejects_later_variable_escaping() {
    let mut s = State::new(10_000);
    let m = s.meta(&vec![], u(1));
    let later = local(s.fresh());
    assert_eq!(s.unify(&m, &later), Err(Error::ScopeEscape));
}
#[test]
fn scope_check_looks_inside_other_meta_spines() {
    let mut s = State::new(10_000);
    let outer = s.meta(&vec![], u(1));
    let (ctx, _) = s.bind(&vec![], "later", u(1));
    let inner = s.meta(&ctx, u(1));
    assert_eq!(s.unify(&outer, &inner), Err(Error::ScopeEscape));
}
#[test]
fn contextual_solution_is_renamed_at_each_occurrence() {
    let mut s = State::new(10_000);
    let (ctx, original) = s.bind(&vec![], "A", u(1));
    let m = s.meta(&ctx, u(1));
    let new = s.fresh();
    let occurrence = s.replace(&m, original, local(new)).unwrap();
    s.unify(&occurrence, &local(new)).unwrap();
    assert_eq!(s.whnf(&m).unwrap(), local(original));
    assert_eq!(s.whnf(&occurrence).unwrap(), local(new));
}
#[test]
fn rejects_non_variable_and_repeated_spines() {
    let mut s = State::new(10_000);
    let (ctx, a) = s.bind(&vec![], "A", u(1));
    let (ctx, b) = s.bind(&ctx, "B", u(1));
    let m = s.meta(&ctx, u(1));
    let repeated = s.replace(&m, b, local(a)).unwrap();
    assert_eq!(s.unify(&repeated, &local(a)), Err(Error::NonPattern));
    let concrete = s.replace(&m, a, u(0)).unwrap();
    assert_eq!(s.unify(&concrete, &u(0)), Err(Error::NonPattern));
}
#[test]
fn accepts_bound_variables_inside_solutions() {
    let mut s = State::new(10_000);
    let m = s.meta(&vec![], u(1));
    let id = s.fresh();
    let rhs = Term::Pi {
        id,
        plicity: Plicity::Explicit,
        domain: u(0),
        body: local(id),
    }
    .arc();
    s.unify(&m, &rhs).unwrap();
    s.finish(m, u(1), &Kernel::default()).unwrap();
}
#[test]
fn expected_meta_type_is_rechecked_even_if_meta_is_unused() {
    let mut s = State::new(10_000);
    let m = s.meta(&vec![], u(0));
    s.unify(&m, &u(0)).unwrap(); // This candidate has the wrong universe.
    assert!(matches!(
        s.finish(u(0), u(1), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
}
#[test]
fn kernel_sees_invalid_subterms_before_beta_reduction() {
    let mut s = State::new(10_000);
    let id = s.fresh();
    let invalid = Term::App(
        Term::Lam {
            id,
            plicity: Plicity::Explicit,
            domain: u(0),
            body: u(0),
        }
        .arc(),
        u(0),
    )
    .arc();
    // Beta reduction would hide the ill-typed argument Type0 : Type0.
    assert!(matches!(
        s.finish(invalid, u(1), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
}
#[test]
fn kernel_rechecks_final_claimed_type() {
    let mut s = State::new(10_000);
    assert!(matches!(
        s.finish(u(0), u(0), &Kernel::default()),
        Err(Error::Kernel(_))
    ));
}
#[test]
fn substitution_avoids_capture() {
    let mut s = State::new(10_000);
    let a = s.fresh();
    let b = s.fresh();
    let term = Term::Lam {
        id: b,
        plicity: Plicity::Explicit,
        domain: u(0),
        body: local(a),
    }
    .arc();
    let result = s.replace(&term, a, local(b)).unwrap();
    let Term::Lam { id, body, .. } = result.as_ref() else {
        panic!()
    };
    assert_ne!(*id, b);
    assert_eq!(body, &local(b));
}
