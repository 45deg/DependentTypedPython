use deppy_core::Term;
use deppy_elab::{
    Elaborator, Expr as E,
    Plicity::{Explicit, Implicit},
    RecordDecl,
};
fn n(name: &str) -> E {
    E::name(name)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut elab = Elaborator::default();
    let record = elab.declare_record(
        1,
        RecordDecl {
            parameters: vec![("T".into(), E::Universe(0))],
            fields: vec![
                ("n".into(), E::Nat),
                ("value".into(), E::vec(n("T"), n("n"))),
            ],
            level: 0,
        },
    )?;
    let sigma = E::sigma("k", E::Nat, E::vec(n("T"), n("k")));
    let pack = E::lam(
        "T",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "n",
            Explicit,
            Some(E::Nat),
            E::lam(
                "xs",
                Explicit,
                Some(E::vec(n("T"), n("n"))),
                E::pair(n("n"), n("xs")).ann(sigma.clone()),
            ),
        ),
    );
    let as_record = E::lam(
        "T",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "p",
            Explicit,
            Some(sigma.clone()),
            record.constructor().app(n("p").fst()).app(n("p").snd()),
        ),
    );
    let as_pair = E::lam(
        "T",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "r",
            Explicit,
            Some(record.ty().implicit(n("T"))),
            E::pair(
                record.projection("n")?.app(n("r")),
                record.projection("value")?.app(n("r")),
            )
            .ann(sigma),
        ),
    );
    for function in [&pack, &as_record, &as_pair] {
        elab.infer(function)?;
    }
    let one = E::Zero.succ();
    let xs = E::vcons(E::Nat, E::Zero, one.clone(), E::vnil(E::Nat));
    let r = as_record.app(pack.app(one).app(xs.clone()));
    let first = elab.infer(&record.projection("n")?.app(r.clone()))?;
    let second = elab.infer(&as_pair.app(r).snd())?;
    assert_eq!(
        elab.kernel().normalize(&first.term)?,
        Term::Succ(Term::Zero.arc()).arc()
    );
    assert_eq!(
        elab.kernel().normalize(&second.term)?,
        elab.infer(&xs)?.term
    );
    println!("Kernel-checked SomeVec: r.n = 1; as_pair(r).snd = [1]");
    println!("pack, as_record and as_pair checked for arbitrary T and vector length");
    Ok(())
}
