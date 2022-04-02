// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

#[pure]
#[trusted]
fn empty() -> (u32, u32) {
    (2, 2)
}

#[requires(Map::<u32, u32>::empty() == Map::<u32, u32>::empty())]
fn test1() {}

#[requires(empty() == empty())]
fn test2() {}

fn checks_preconditions() {
    test1();
}

fn main() {}
