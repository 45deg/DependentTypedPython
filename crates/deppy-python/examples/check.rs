use deppy_core::Term;
use deppy_elab::Expr as E;
use deppy_python::{check_module, Target};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let module = check_module(include_str!("basics.py"), Target::Python314)?;
    let e = &module.elaborator;
    let result = e.infer(&E::name("twice").app(E::Zero))?;
    assert_eq!(
        e.kernel().normalize(&result.term)?,
        Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
    );
    let proof = e.infer(&E::name("reflexive").app(E::Zero))?;
    assert_eq!(
        e.kernel().normalize(&proof.term)?,
        Term::Refl {
            ty: Term::Nat.arc(),
            value: Term::Zero.arc()
        }
        .arc()
    );
    println!(
        "Checked {} Python declarations; twice(Z) = S(S(Z)), reflexive(Z) = refl(Z)",
        module.definitions.len()
    );
    Ok(())
}
