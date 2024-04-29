use prusti_contracts::*;

struct Pair<T, U>(T, U);

#[pure]
fn pair<T, U>(x: T, y: U) -> Pair<T, U> {
    Pair(x, y)
}

#[ensures(pair(1, true).0 == 1)]
#[ensures(pair(1, true).1 == true)]
fn main() {}
