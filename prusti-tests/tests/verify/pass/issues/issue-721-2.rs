// compile-flags: -Pverification_deadline=5

use prusti_contracts::*;
use std::convert::TryFrom;

#[trusted]
#[requires(s.len() == 16)]
#[ensures(forall(|i: usize| (0 <= i && i < 16) ==> (old(s[i]) == result[i] )))]
#[ensures(result[0] > 100)]
pub fn slice_to_array16(s: &[i32]) -> [i32; 16] {
     <[i32; 16]>::try_from(s).unwrap()
}

#[requires(forall(|i: usize| (0 <= i && i < 16) ==> (a[i] > 100)))]
#[requires(a[0] > 100)]
pub fn foo(a: [i32; 16]) {
    let s: &[i32] = &a;
    let a2: [i32; 16] = slice_to_array16(s);
    assert!(a2[0] > 100);
}

fn main() {}
