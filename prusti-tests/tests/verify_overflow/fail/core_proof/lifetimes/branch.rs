// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

fn branch_borrow(c: bool){
    let mut a: i32 = 4;
    let mut b: i32 = 5;
    let x;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
}
fn branch_borrow_assert_false(c: bool){
    let mut a: i32 = 4;
    let mut b: i32 = 5;
    let x;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn branch_borrow_assign(c: bool) {
    let mut a: i32 = 1;
    let mut b: i32 = 1;
    let x;
    if c {
        x = &mut a;
        *x = 2;
    } else {
        x = &mut b;
        *x = 3;
    }
    *x = 4;
}
fn branch_borrow_assign_assert_false(c: bool) {
    let mut a: i32 = 1;
    let mut b: i32 = 1;
    let x;
    if c {
        x = &mut a;
        *x = 2;
    } else {
        x = &mut b;
        *x = 3;
    }
    *x = 4;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn branch_borrow_with_fixed_type(c: bool){
    let mut a: i32 = 4;
    let mut b: i32 = 5;
    let x: &mut i32;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
    *x = 6;
}
fn branch_borrow_with_fixed_type_assert_false(c: bool){
    let mut a: i32 = 4;
    let mut b: i32 = 5;
    let x: &mut i32;
    if c {
        x = &mut a;
    } else {
        x = &mut b;
    }
    *x = 6;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
