// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

enum Something {
    First,
    Second,
    Third,
}

#[ensures(result)]
fn test1(x: Something) -> bool {
    !matches!(x, Something::Third)
}

#[ensures(result)]
fn test2(x: Something, y: Something) -> bool {
    matches!(x, Something::First) || !matches!(y, Something::First)
}

fn main() {}
