use deppy_core::{Kernel, Relevance, Term};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Fully explicit core of: def identity[A: Type](x: A) -> A: return x
    let identity = Term::Lam {
        relevance: Relevance::Erased,
        domain: Term::Universe(0).arc(),
        body: Term::Lam {
            relevance: Relevance::Runtime,
            domain: Term::Var(0).arc(),
            body: Term::Var(0).arc(),
        }
        .arc(),
    }
    .arc();
    let kernel = Kernel::default();
    let ty = kernel.infer(&identity)?;
    kernel.check(&identity, &ty)?;
    println!("identity type: {ty:#?}");
    println!("type universe: {:?}", kernel.infer(&ty)?);
    Ok(())
}
