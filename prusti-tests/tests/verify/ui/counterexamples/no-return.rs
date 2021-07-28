// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

fn test1(x: i32, y: i32) {
    let z = if x == 42 {
        35
    } else {
        x + 4
    };
    assert!(z != y + 5);
}

fn main() {}
