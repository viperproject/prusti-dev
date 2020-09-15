#![feature(attr_literals)]

use prusti_contracts::*;

// no args
#[ensures()]
fn no_args() {}

#[requires("too", "many", "args")]
fn too_many_args() {}

#[requires("true")]
fn wrong_token() {
    let mut i=0u32;
    #[invariant["true"]]
    while i<10 {
        i += 1
    }
}

fn main() {}