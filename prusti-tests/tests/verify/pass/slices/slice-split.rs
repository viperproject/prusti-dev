use prusti_contracts::*;

fn main() {
    let a = [0; 13];
    let (s0, s1) = split_at(&a, 7);

    assert!(s0.len() == 7);
    assert!(s1.len() == 6);

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
