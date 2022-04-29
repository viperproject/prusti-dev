use prusti_contracts::*;

trait Trait<Tp> {
    #[ensures(true)]
    fn fn1<Tx, Ty, Tz>();
}

struct Struct<Ex, Ey> { x: Ex, y: Ey }

impl<A, B, C> Trait<A> for Struct<B, C> {
    // inherit spec
    fn fn1<X, Y, Z>() {}
}

fn main() {}
