// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(4 * n as usize + 2))]
#[ensures(time_receipts(4 * n as usize + 2))]
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits(4 * (n - i) as usize));
        body_invariant!(time_receipts(4 * i as usize + 2));
        res += i;
        i += 1;
    }
    res
}

fn main() {
    // sum(4);
}
