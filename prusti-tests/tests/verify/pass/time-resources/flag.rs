use prusti_contracts::*;

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        res += i;
        i += 1;
    }
    res
}

fn main() {
    // sum(4);
}
