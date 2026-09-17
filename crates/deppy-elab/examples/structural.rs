use deppy_elab::{prelude::structural, Elaborator, Expr as E};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let elab = Elaborator::default();
    // These definitions contain constructor branches and checked self-calls,
    // rather than explicit motives or induction-hypothesis parameters.
    let append = E::Core(elab.compile_function(&structural::append(0))?.term);
    let get = E::Core(elab.compile_function(&structural::get(0))?.term);
    let zero_right = E::Core(elab.compile_function(&structural::zero_right())?.term);
    let one = E::Zero.succ();
    let xs = E::vcons(E::Nat, E::Zero, one.clone(), E::vnil(E::Nat));
    let ys = E::vcons(E::Nat, E::Zero, E::Zero, E::vnil(E::Nat));
    let joined = append
        .app(one.clone())
        .app(one.clone())
        .app(xs)
        .app(ys.clone());
    let value = elab.infer(&joined)?;
    let expected = elab.infer(&E::vcons(E::Nat, one.clone(), one.clone(), ys))?;
    assert_eq!(elab.kernel().normalize(&value.term)?, expected.term);
    let selected = elab.infer(
        &get.app(one.clone().succ())
            .app(joined)
            .app(E::fs(one.clone(), E::fz(E::Zero))),
    )?;
    assert_eq!(
        elab.kernel().normalize(&selected.term)?,
        elab.infer(&E::Zero)?.term
    );
    let proof = elab.infer(&zero_right.app(one.clone()))?;
    assert_eq!(
        elab.kernel().normalize(&proof.term)?,
        elab.infer(&one.refl())?.term
    );
    println!("Lowered structural append: [1] ++ [0] = [1, 0]");
    println!("Lowered nested get: index 1 selects 0");
    println!("Lowered induction: zero_right(1) computes to refl(1)");
    Ok(())
}
