// compile-flags: -Pcounterexample=true
// normalize-stderr-test: "final value:\s*-?[0-9]+" -> "$(FINAL_VALUE)"

use prusti_contracts::*;

#[ensures(result != 16)]
fn spurious() -> i32 {
    let mut x = 10;
    let mut y = 1;
    while (x > 0) {
        // The invariant is too weak to guarantee the postcondition even though
        // the program does.
        body_invariant!(x >= 0 && y > 0);
        x = x - 1;
        y = y + 1;
    }
    y
}

fn main() {}
