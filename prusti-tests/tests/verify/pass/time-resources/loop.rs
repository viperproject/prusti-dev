// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(n as usize + 1))]
#[ensures(time_receipts(n as usize + 1))]
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits((n - i) as usize));
        body_invariant!(time_receipts(i as usize + 1));
        res += i;
        i += 1;
    }
    res
}

#[requires(time_credits(n as usize + 1))]
#[ensures(time_receipts(n as usize + 1))]
fn sum2(n: u32) -> u32 {
    let mut i = n; // To be correct it should be n
    let mut res = 0;
    while 0 < i {
        body_invariant!(time_credits(i as usize));
        body_invariant!(time_receipts(1 + (n - i) as usize));
        res += i;
        i -= 1;
    }
    res
}

#[requires(time_credits(12))]
#[ensures(time_receipts(12))]
fn main() {
    sum(10);
}
