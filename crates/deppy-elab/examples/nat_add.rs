use deppy_core::{Kernel, Term};
use deppy_elab::{prelude::nat_add, Elaborator, Expr};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let two = Expr::Zero.succ().succ();
    let three = two.clone().succ();
    let result = Elaborator::default().infer(&nat_add().app(two).app(three))?;
    let kernel = Kernel::default();
    let normal = kernel.normalize(&result.term)?;
    let five = (0..5).fold(Term::Zero.arc(), |n, _| Term::Succ(n).arc());
    assert_eq!(normal, five);
    assert_eq!(kernel.normalize(&result.ty)?, Term::Nat.arc());
    println!("Kernel-checked Nat addition: 2 + 3 = 5");
    println!("Normal form: {normal:?}");
    Ok(())
}
