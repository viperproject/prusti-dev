// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

pub enum Choose {
    One,
    Two { x: i32, y: bool },
    Three(char, bool),
}

#[ensures(result)]
fn test1(x: Choose) -> bool {
    match x {
        Choose::One => true,
        Choose::Two { x, y } => true,
        Choose::Three(c, d) => c != 'c' || d,
    }
}

fn main() {}
