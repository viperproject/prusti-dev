use prusti_contracts::*;

trait Trait<'a> {
    type AT;
}

fn test<'a, T: Trait<'a>>(_t: T) -> T::AT {
    unimplemented!()
}

#[trusted]
fn main() {}
