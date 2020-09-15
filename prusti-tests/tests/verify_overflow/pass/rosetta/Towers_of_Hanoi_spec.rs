//! An adaptation of the example from
//! http://rosettacode.org/wiki/Towers_of_Hanoi#Rust
//!
//! Changes:
//!
//! +   Replaced ``println!`` with calling trusted functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//! +   The `print_move` function is called with valid, different, poles

use prusti_contracts::*;

#[pure]
fn valid_pole(x: i32) -> bool {
    x == 1 || x == 2 || x == 3
}

#[trusted]
#[requires(valid_pole(from) && valid_pole(to) && from != to)]
fn print_move(from: i32, to: i32) {
    println!("Move disk from pole {} to pole {}", from, to);
}

#[requires(n >= 0)]
#[requires(valid_pole(from) && valid_pole(to) && valid_pole(via))]
#[requires(from != to && to != via && via != from)]
fn move_(n: i32, from: i32, to: i32, via: i32) {
    if n > 0 {
        move_(n - 1, from, via, to);
        print_move(from, to);
        move_(n - 1, via, to, from);
    }
}

fn main() {
    move_(4, 1,2,3);
}
