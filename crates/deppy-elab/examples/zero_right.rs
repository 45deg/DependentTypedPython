use deppy_core::{Kernel, Term};
use deppy_elab::{
    prelude::{nat_add, zero_right},
    Elaborator, Expr as E,
    Plicity::Explicit,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let elab = Elaborator::default();
    let expected = E::pi(
        "n",
        Explicit,
        E::Nat,
        E::eq(
            E::Nat,
            nat_add().app(E::name("n")).app(E::Zero),
            E::name("n"),
        ),
    );
    elab.check(&zero_right(), &expected)?;
    let two = E::Zero.succ().succ();
    let proof = elab.infer(&zero_right().app(two))?;
    let normal = Kernel::default().normalize(&proof.term)?;
    assert_eq!(
        normal,
        Term::Refl {
            ty: Term::Nat.arc(),
            value: Term::Succ(Term::Succ(Term::Zero.arc()).arc()).arc()
        }
        .arc()
    );
    println!("Kernel-checked induction: (n : Nat) -> Eq Nat (add n Z) n");
    println!("zero_right(2) normalizes to refl(2)");
    Ok(())
}
