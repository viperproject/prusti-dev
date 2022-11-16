// compile-flags: -Pverification_deadline=25

use prusti_contracts::*;

fn main() {
    let a = [0; 13];
    let (s0, s1) = split_at(&a, 7);

    assert!(s0.len() == 7);
    assert!(s1.len() == 6);

    // these 2 dummy assertions are needed to trigger the quantifiers from split_at().
    // without it, the next block of assertions won't be verified by Prusti.
    // Issue: https://github.com/viperproject/prusti-dev/issues/812
    assert!(a[2] == s0[2]);
    assert!(a[9] == s1[2]);

    assert!(s0[2] == 0);
    assert!(s1[2] == 0);
}

#[trusted]
#[requires(0 <= idx && idx < slice.len())]
#[ensures(result.0.len() == idx)]
#[ensures(result.1.len() == slice.len() - idx)]
#[ensures(forall(|i: usize| (0 <= i && i < idx) ==> slice[i] == result.0[i]))]
#[ensures(forall(|i: usize, j: usize| (idx <= i && i < slice.len() && 0 <= j && j < result.1.len()) ==> slice[i] == result.1[j]))]
fn split_at(slice: &[i32], idx: usize) -> (&[i32], &[i32]) {
    slice.split_at(idx)
}
