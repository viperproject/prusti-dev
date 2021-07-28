// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[requires(x == -1)] // force specific counterexample
#[ensures(false)]
fn test1(x: i32) -> i32 {
    if x > 0 {
        return 3;
    }
    let y = 5 + x;
    y * 2
}

fn main() {}
