// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// #[requires(n > 0)]
#[requires(time_credits(n as usize + 2))]
#[ensures(time_receipts(n as usize + 1))] //~ ERROR Not enough time receipts
fn sum(n: u32) -> u32 {
    let mut i = 1; // To be correct it should be n
    let mut res = 0;
    while 0 < i {
        body_invariant!(time_credits(i as usize));
        body_invariant!(time_receipts(1 + (n - i) as usize)); //~ ERROR Not enough time receipts
        res += i;
        i -= 1;
    }
    res
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn main() {}
