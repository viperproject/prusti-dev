// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[requires(b == 0)] // force specific counterexample
#[ensures(result != 3)] 
fn foo(a: i32, b: i32) -> i32 {
    if a == 42 {
        let b = 3;
        b
    } else {
        let a = 46;
        a
    }
}

fn main() {}
