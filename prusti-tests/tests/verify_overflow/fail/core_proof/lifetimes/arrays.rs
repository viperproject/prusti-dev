// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

fn array_borrow() {
    let mut a = [1; 4];
    let b = &mut a[2];
    *b = 2;
}

fn array_borrow_assert_false() {
    let mut a = [1; 4];
    let b = &mut a[2];
    *b = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn array_reborrow_and_assign() {
    let mut a = [1; 4];
    let b = &mut a[2];
    let c = &mut *b;
    *c = 2;
}

fn array_reborrow_and_assign_assert_false() {
    let mut a = [1; 4];
    let b = &mut a[2];
    let c = &mut *b;
    *c = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
