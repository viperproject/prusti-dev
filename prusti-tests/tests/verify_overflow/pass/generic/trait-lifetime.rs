use prusti_contracts::*;

trait Trait<'a> {
    type AT;
}

#[trusted]
fn test1<'a, T: Trait<'a>>(_t: T) -> T::AT {
    unimplemented!()
}

fn test2<'a, T: Trait<'a>>(x: T) {
    test1(x);
}

#[trusted]
fn main() {}
