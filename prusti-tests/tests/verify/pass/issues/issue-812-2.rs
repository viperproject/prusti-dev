use prusti_contracts::*;

fn main() {}

#[requires(forall(|i: usize| (0 <= i && i < array.len()) ==> (array[i] > 10), triggers=[(array[i],)]))]
fn test(array: &[i32; 10]) {}
