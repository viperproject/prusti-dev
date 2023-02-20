use prusti_contracts::*;

#[pure]
fn something_true() -> bool {
    true
}

#[ensures(something_true() && false)]
fn client(a: u32) {}

#[pure]
#[ensures(result)]
fn test1() -> bool {
    false
}

#[pure]
#[ensures(x)]
fn test2(x: bool) -> bool {
    x
}

#[ensures(a === b)]
fn test3<T>(a: T, b: T) {}

fn main() {}
