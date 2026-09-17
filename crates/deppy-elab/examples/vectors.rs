use deppy_core::Kernel;
use deppy_elab::{
    prelude::{vec_append, vec_get},
    Elaborator, Expr as E,
};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let elab = Elaborator::default();
    let k = Kernel::default();
    let one = E::Zero.succ();
    let two = one.clone().succ();
    let xs = E::vcons(E::Nat, E::Zero, one.clone(), E::vnil(E::Nat));
    let ys = E::vcons(E::Nat, E::Zero, E::Zero, E::vnil(E::Nat));
    let joined = vec_append(0)
        .app(one.clone())
        .app(one.clone())
        .app(xs)
        .app(ys.clone());
    let out = elab.infer(&joined)?;
    let expected = elab.infer(&E::vcons(E::Nat, one.clone(), one.clone(), ys))?;
    assert_eq!(k.normalize(&out.term)?, expected.term);
    let second = E::fs(one, E::fz(E::Zero));
    let out = elab.infer(&vec_get(0).app(two).app(joined).app(second))?;
    assert_eq!(k.normalize(&out.term)?, elab.infer(&E::Zero)?.term);
    println!("Kernel-checked append: [1] ++ [0] = [1, 0]");
    println!("Kernel-checked get: Fin[2] index 1 selects 0");
    Ok(())
}
