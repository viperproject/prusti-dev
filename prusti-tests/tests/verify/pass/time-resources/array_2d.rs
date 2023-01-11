// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// ignore-test: loop place context issues and mixed dereferencing and array indexing projections are not supported

#[requires(a.len() > 0)]
#[requires(forall(|i: usize| i < a.len() ==> a[i].len() == a[0].len()))]
#[requires(time_credits(a.len() * a[0].len() + 1))]
#[ensures(time_receipts(a.len() * a[0].len() + 1))]
fn sum_2d(a: &[&[u32]]) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < a.len() {
        body_invariant!(time_credits((a.len() - i) * a[i].len()));
        body_invariant!(time_receipts(i * a[i].len()));
        let mut j = 0;
        while j < a[i].len() {
            body_invariant!(time_credits(a[i].len() - j));
            body_invariant!(time_receipts(j));
            res += a[i][j];
            j += 1;
        }
        i += 1;
    }
    res
}

#[requires(time_credits(1))]
fn main() {}
