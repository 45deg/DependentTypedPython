use deppy_elab::{
    Elaborator, Expr as E,
    Plicity::{Explicit, Implicit},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Programmatic input AST; a Python frontend will produce this information.
    // identity : {A : Type0} -> A -> A
    let identity = E::lam(
        "A",
        Implicit,
        Some(E::Universe(0)),
        E::lam("x", Explicit, Some(E::name("A")), E::name("x")),
    );
    // Under B : Type0, value : B, infer the omitted argument in identity(value).
    let call = E::lam(
        "B",
        Implicit,
        Some(E::Universe(0)),
        E::lam(
            "value",
            Explicit,
            Some(E::name("B")),
            identity.app(E::name("value")),
        ),
    );
    let result = Elaborator::default().infer(&call)?;
    println!(
        "kernel-checked core (including the inferred type argument):\n{:#?}",
        result.term
    );
    println!("type:\n{:#?}", result.ty);
    Ok(())
}
