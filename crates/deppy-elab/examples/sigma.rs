use deppy_core::{Kernel, Term};
use deppy_elab::{
    Elaborator, Expr as E,
    Plicity::{Explicit, Implicit},
};
fn n(name: &str) -> E {
    E::name(name)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let elab = Elaborator::default();
    let kernel = Kernel::default();
    // pack : {A : Type0} -> (n : Nat) -> Vec A n -> Sigma k : Nat. Vec A k
    let pack = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "n",
            Explicit,
            Some(E::Nat),
            E::lam(
                "xs",
                Explicit,
                Some(E::vec(n("A"), n("n"))),
                E::pair(n("n"), n("xs")).ann(E::sigma("k", E::Nat, E::vec(n("A"), n("k")))),
            ),
        ),
    );
    elab.infer(&pack)?;
    let xs = E::vcons(E::Nat, E::Zero, E::Zero.succ(), E::vnil(E::Nat));
    let packed = pack.app(E::Zero.succ()).app(xs.clone());
    let first = elab.infer(&packed.clone().fst())?;
    let second = elab.infer(&packed.snd())?;
    assert_eq!(
        kernel.normalize(&first.term)?,
        Term::Succ(Term::Zero.arc()).arc()
    );
    assert_eq!(kernel.normalize(&second.term)?, elab.infer(&xs)?.term);
    assert_eq!(
        kernel.normalize(&second.ty)?,
        elab.infer(&E::vec(E::Nat, E::Zero.succ()))?.term
    );
    println!("Kernel-checked pack: Pair(1, [1]) : Sigma k : Nat. Vec Nat k");
    println!("fst = 1; snd = [1] : Vec Nat 1");
    Ok(())
}
