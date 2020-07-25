extern crate prusti_contracts;

// ignore-test Unsupported loop. We don't yet generate magic wands in loop invariants, which are
// required when a loan is created before, and expires after, the loop invariant.

fn test_borrow_in_guard() {
    let mut x: &mut Box<i32>;
    let mut y = Box::new(123);
    while {
        x = &mut y;
        true
    } {
        drop(x);
    }
}

fn main() {}
