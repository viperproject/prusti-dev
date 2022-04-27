// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

#[requires(Map::<u32, u32>::empty() == Map::<u32, u32>::empty())]
fn test1() {}

fn checks_preconditions() {
    test1();
}

fn main() {}
