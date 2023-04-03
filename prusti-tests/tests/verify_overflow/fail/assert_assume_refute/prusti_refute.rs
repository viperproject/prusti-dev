#![allow(unused)]

use prusti_contracts::*;

fn refute1() {
    prusti_refute!(false);
}

fn failing_refute() {
    prusti_refute!(true); //~ ERROR
}

fn unreachable_branch_sign(val: i32) -> i32 {
    if val <= 0 {
        -1
    } else if val >= 0 {
        1
    } else {
        prusti_refute!(false); //~ ERROR
        0
    }
}

#[requires(val < 0 && val > 0)]
fn no_valid_input(val: i32) -> i32 {
    prusti_refute!(false); //~ ERROR
    42
}

fn main() {}
