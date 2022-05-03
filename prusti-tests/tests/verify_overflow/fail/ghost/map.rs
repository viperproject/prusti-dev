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

fn ghost() {
    let mut x = 0;
    ghost! {
        x = 1;
    }
    assert!(x == 1);
}

#[ensures(Map::empty().insert(0, 0) == Map::<u32, u32>::empty())]
fn should_fail(){}

fn main() {}
