use prusti_contracts::*;

fn main() {}

#[requires(forall(|i: usize| (0 <= i && i < slice.len()) ==> (slice[i] > 10), triggers=[(slice[i],)]))]
fn test(slice: &[i32]) {}
