use prusti_contracts::*;

struct Pair<T, U> {
    a: T,
    b: U,
}

fn consume<U>(x: U) {}

fn test2<U: Clone>(pair: &mut Pair<i8, U>) {
    let x = pair.b.clone();
    consume(x);
}

fn main() {}
