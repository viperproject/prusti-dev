// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(bound + 1))]
#[ensures(time_receipts(result.0 + 1))]
#[ensures(a.len() >= bound ==> result.0 == bound)]
#[ensures(a.len() <= bound ==> result.0 == a.len())]
fn bounded_sum(a: &[usize], bound: usize) -> (usize, usize) {
    let mut i = 0;
    let mut sum = 0;
    while i < a.len() && i < bound {
        body_invariant!(time_credits(bound - i));
        body_invariant!(time_receipts(i));
        sum += a[i];
        i += 1;
    }
    (i, sum)
}

#[requires(time_credits(a.len() + 2))]
#[ensures(time_receipts(a.len() + 2))]
fn sum(a: &[usize]) -> usize {
    bounded_sum(a, a.len()).1
}

#[requires(a.len() >= 1)]
#[requires(time_credits(3))]
#[ensures(time_receipts(3))]
fn first(a: &[usize]) -> usize {
    bounded_sum(a, 1).1
}

#[requires(time_credits(9))]
#[ensures(time_receipts(9))]
fn main() {
    let a = [1, 2, 3];
    let _s = sum(&a);
    let _f = first(&a);
}
