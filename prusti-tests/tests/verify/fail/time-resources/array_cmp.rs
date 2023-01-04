// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(a.len() == b.len())]
#[requires(time_credits(a.len() + 1))]
#[ensures(time_receipts(a.len() + 1))] 
fn opt_array_cmp<T: Eq>(a: &[T], b: &[T]) -> bool { //~ ERROR Not enough time receipts at the end of the function.
  let mut i = 0;
  while i < a.len() {
    if a[i] != b[i] {
      return false;
    }
    i += 1;
  }
  return true;
}

#[requires(time_credits(1))]
fn main() {}