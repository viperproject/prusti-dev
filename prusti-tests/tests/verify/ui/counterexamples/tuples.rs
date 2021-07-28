// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[requires(x.0 > 0 && x.0 < 2 && x.1 == 'c')] // force specific counterexample
#[ensures(result.1 >= 0)]
fn test1(x: (i32, char)) -> (char, i32) {
    let y = x.0 - 2;
    let z = x.1;
    (z, y)
}

#[requires(x.0 == 5 && x.1 == 6)] // force specific counterexample
fn test2(x: (i32, i32)) {
    assert!(x.0 == x.1);
}

fn test3(x: (i32, bool)) {
    if x.0 == 32 {
        if !x.1 {
            assert!(x.0 == 0);
        }
    }
}

fn main() {}
