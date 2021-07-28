// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

enum Choose {
    One,
    Two(i32),
    Three(bool),
}

#[ensures(result)]
fn test1(x: Choose) -> bool {
    match x {
        Choose::One => true,
        Choose::Two(x) => x < -3 || x > -3,
        Choose::Three(b) => true,
    }
}

fn main() {}
