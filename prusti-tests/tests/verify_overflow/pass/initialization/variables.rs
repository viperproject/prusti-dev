#![feature(nll)]

use prusti_contracts::*;

fn test3() {
    let x = 5;
    if false {
        let y = 4;
        assert!(y == 4);
    }
    let z = 3;
    assert!(x == 5);
    assert!(z == 3);
}

fn main() {}
