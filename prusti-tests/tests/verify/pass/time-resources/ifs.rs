// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(n as usize + 1))]
#[ensures(time_receipts(n as usize + 1))]
fn sum(n: u32) -> u32 {
    let mut i = n;
    let mut res = 0;
    while 0 < i {
        body_invariant!(time_credits(i as usize));
        body_invariant!(time_receipts(1 + (n - i) as usize));
        res += i;
        i -= 1;
    }
    res
}

#[requires(time_credits(if b { 1 } else { n as usize + 2}))]
#[ensures(time_receipts(if b { 1 } else { n as usize + 2}))]
fn foo(b: bool, n: u32) -> u32 {
    if b {
        42
    } else {
        sum(n)
    }
}

#[requires(time_credits(n as usize + 2))]
#[ensures(time_receipts(1))]
fn bar(b: bool, n: u32) -> u32 {
    if b {
        42
    } else {
        sum(n)
    }
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn main() {}
