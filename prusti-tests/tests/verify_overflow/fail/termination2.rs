// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;

fn main() {}

#[requires(x < 100_000)]
#[requires(x >= 0)]
#[terminates(Int::new(x))]
fn y1(x: i64) {
    if x > 0 {
        y2(x - 1)
    }
}

#[requires(x < 100_000)]
#[requires(x >= 0)]
#[terminates(Int::new(x))]
fn y2(x: i64) {
    if x > 0 {
        y1(x - 1)
    }
    z(x * 100)
}

#[terminates(Int::new(x))]
fn z(x: i64) {
    if x > 0 {
        z(x - 1)
    }
}

#[terminates]
fn nonterminating() {
    nonterminating() //~ ERROR
}

#[pure]
fn pure_implies_termination() {
    pure_implies_termination() //~ ERROR
}
