// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

pub fn mutable_borrow() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    assert!(*x == 2);
}

pub fn mutable_borrow_assert_false() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    assert!(*x == 4);      //~ ERROR: the asserted expression might not hold
}

pub fn mutable_borrow_2() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    assert!(*x == 2);
    assert!(a == 2);
}

pub fn mutable_borrow_2_assert_false() {
    let mut a = 4;
    let x = &mut a;
    *x = 2;
    assert!(a == 4);      //~ ERROR: the asserted expression might not hold
}

pub fn mutable_reborrow() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    assert!(*y == 3);
}

pub fn mutable_reborrow_assert_false() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    assert!(*y == 4);      //~ ERROR: the asserted expression might not hold
}

pub fn mutable_reborrow_2() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    assert!(*y == 3);
    assert!(a == 3);
}

pub fn mutable_reborrow_2_assert_false() {
    let mut a = 4;
    let mut x = &mut a;
    let y = &mut (*x);
    *y = 3;
    assert!(*y == 3);
    assert!(a == 4);      //~ ERROR: the asserted expression might not hold
}

pub fn shared_borrow() {
    let mut a = 4;
    let x = &a;
    let y = &a;
    assert!(*y == 4);
}

pub fn shared_borrow_assert_false() {
    let mut a = 4;
    let x = &a;
    let y = &a;
    assert!(*y == 5);      //~ ERROR: the asserted expression might not hold
}

pub fn shared_reborrow() {
    let mut a = 4;
    let x = &a;
    let y = &(*x);
    let z = &(*x);
    assert!(*z == 4);
}

pub fn shared_reborrow_assert_false() {
    let mut a = 4;
    let x = &a;
    let y = &(*x);
    let z = &(*x);
    assert!(*z == 5);      //~ ERROR: the asserted expression might not hold
}

pub fn simple_references() {
    let mut a = 4;
    let mut b = &mut a;
    let mut c = &mut b;
    let mut d = &mut c;
}

pub fn simple_references_assert_false() {
    let mut a = 4;
    let mut b = &mut a;
    let mut c = &mut b;
    let mut d = &mut c;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

// FIXME: Fix overlapping shared references
// pub fn shared_borrow() {
//     let mut a = 4;
//     let x = &a;
//     let y = &a;
//     assert!(*x == 4);
// }
