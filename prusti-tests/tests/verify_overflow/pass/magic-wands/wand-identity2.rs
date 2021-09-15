#![allow(dead_code)]

use prusti_contracts::*;

struct T {
    val: i32
}

#[after_expiry(x.val == before_expiry(result.val))]
fn identity(x: &mut T) -> &mut T {
    x
}

fn identity_use() {
    let mut t = T { val: 5 };
    let y = &mut t;
    let z = identity(y);
    z.val = 6;
    assert!(t.val == 6);
}

#[ensures(result.val == v)]    // TODO x.val is illegal, but Prusti doesn't report a readable error message.
#[after_expiry(x.val == before_expiry(result.val))]
fn identity2(x: &mut T, v: i32) -> &mut T {
    x.val = v;
    x
}

#[ensures(*result == v)]
#[after_expiry(x.val == before_expiry(*result))]
fn identity3(x: &mut T, v: i32) -> &mut i32 {
    x.val = v;
    &mut x.val
}

fn identity_use2() {
    let mut t = T { val: 5 };
    assert!(t.val == 5);
    let y = &mut t;
    assert!(y.val == 5);
    let z = identity(y);
    z.val = 6;
    let x = identity2(z, 7);
    let v = identity3(x, 8);
    assert!(*v == 8);
    assert!(t.val == 8);
}

fn identity_use3() {
    let mut t = T { val: 5 };
    assert!(t.val == 5);
    let y = &mut t;
    assert!(y.val == 5);
    let z = identity(y);
    z.val = 6;
    let x = identity2(z, 7);
    let v = identity3(x, 8);
    assert!(*v == 8);
    // Failing tests must go to the `tests/verify/fail/` folder
    //assert!(t.val == 9);
}

fn main() {}
