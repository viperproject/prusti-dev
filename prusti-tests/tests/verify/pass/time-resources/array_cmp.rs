// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(a.len() == b.len())]
#[requires(time_credits(a.len() + 1))]
#[ensures(time_receipts(a.len() + 1))]
fn safe_array_cmp<T: Eq>(a: &[T], b: &[T]) -> bool {
    let mut i = 0;
    let mut res = true;
    while i < a.len() {
        body_invariant!(time_credits(a.len() - i));
        body_invariant!(time_receipts(i));
        res &= a[i] == b[i];
        i += 1;
    }
    return res;
}

#[requires(a.len() == b.len())]
#[requires(time_credits(a.len() + 1))]
#[ensures(time_receipts(1))]
fn opt_array_cmp<T: Eq>(a: &[T], b: &[T]) -> bool {
    let mut i = 0;
    while i < a.len() {
        body_invariant!(time_credits(a.len() - i));
        body_invariant!(time_receipts(i));
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    return true;
}

#[requires(time_credits(1))]
fn main() {}
