// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

unsafe fn test_assert1() {
    let a = 5;
    assert!(a == 5);
}

unsafe fn test_assert2() {
    let a = 5;
    assert!(a == 6);    //~ ERROR: the asserted expression might not hold
}

#[trusted]
fn main() {}

