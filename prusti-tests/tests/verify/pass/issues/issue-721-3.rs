// compile-flags: -Pverification_deadline=5

use prusti_contracts::*;

#[requires(forall(|i: usize| (0 <= i && i < 16) ==> (array[i] > 100) ))]
#[requires(array[4] <= usize::MAX)]
#[ensures(result[0] > 100)]
pub fn example(array: &[usize; 16]) -> &[usize] {
    &array[4..8]
}

fn main() {}
