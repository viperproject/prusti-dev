use prusti_contracts::*;

struct Pair<T, U> {
    a: T,
    b: U,
}

#[requires(pair.a == 42)]
fn test2<U>(pair: &mut Pair<i8, U>) {
    assert!(pair.a == 42);
}

fn main() {}
