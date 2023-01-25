//! Assignments to non local variables in pure code are currently not supported,
//! but can be in the future.
use prusti_contracts::*;

#[pure]
fn pure1() -> (u32, u32) {
    let mut x = (1, 2);
    x.1 = 3; //~ ERROR only assignments to local variables are supported in pure code
    x
}

#[pure]
fn pure2() -> (u32, u32) {
    let mut x = (1, 2);
    let y = &mut x.1;
    *y = 3; //~ ERROR only assignments to local variables are supported in pure code
    x
}

fn client1() {
    let x = pure1(); //~ ERROR
    let y = (1, 2);
    assert!(x == y); // Should fail
}

fn client2() {
    let x = pure2(); //~ ERROR
    let y = (1, 2);
    assert!(x == y); // Should fail
}

fn main() {}
