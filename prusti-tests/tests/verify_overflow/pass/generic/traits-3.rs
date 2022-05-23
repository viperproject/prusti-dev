use prusti_contracts::*;

trait Validity {
    #[pure]
    fn valid(&self) -> bool;
}

#[requires(a.valid())]
fn test<T: Validity>(a: T) -> T {
    a
}

fn main() {}
