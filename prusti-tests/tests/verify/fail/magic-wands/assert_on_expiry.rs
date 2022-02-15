#![allow(dead_code)]

use prusti_contracts::*;

struct T {
    val: i32
}

#[assert_on_expiry(result.val == 5, x.val == 5)]
fn identity(x: &mut T) -> &mut T {
    x
}

fn test1() {
    let mut a = T { val: 4 };
    let y = &mut a;
    let z = identity(y);    //~ ERROR: obligation might not hold on borrow expiry
    z.val = 6;
}

fn test2() {
    let mut a = T { val: 4 };
    let y = &mut a;
    let z = identity(y);
    z.val = 5;
}

fn main() {}
