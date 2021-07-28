// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[ensures(result)]
fn test1(b: bool) -> bool {
    !b
}

#[pure]
#[ensures(result)]
fn test2(b: bool) -> bool {
    !b
}

fn test3(b: bool) {
    assert!(b);
}

fn main() {}
