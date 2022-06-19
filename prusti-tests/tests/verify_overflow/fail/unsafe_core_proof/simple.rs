// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

pub fn mutable_borrow() {
    let mut a = 4;
    let x = &mut a;
}
pub fn mutable_borrow_assert_false() {
    let mut a = 4;
    let x = &mut a;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

