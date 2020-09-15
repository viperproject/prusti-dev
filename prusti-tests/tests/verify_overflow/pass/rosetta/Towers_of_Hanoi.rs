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

use prusti_contracts::*;

#[trusted]
fn print_move(from: i32, to: i32) {
    println!("Move disk from pole {} to pole {}", from, to);
}

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
