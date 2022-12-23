// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(if n <= 0 { 1 } else { n as usize + 1}))]
#[ensures(time_receipts(if n <= 0 { 1 } else { n as usize + 1}))]
fn sum(n: i32) -> i32 {
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

#[requires(n <= 0 ==> time_credits(1))]
#[requires(n > 0 ==> time_credits(n as usize + 1))]
#[ensures(n <= 0 ==> time_receipts(1))]
#[ensures(n > 0 ==> time_receipts(n as usize + 1))]
fn sum2(n: i32) -> i32 {
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

#[requires(time_credits(2))]
#[ensures(time_receipts(2))]
fn foo() {
    sum(-12);
}

#[requires(time_credits(1 + 42 + 1 + 2))]
#[ensures(time_receipts(1 + 42 + 1 + 2))]
fn main() {
    sum(42);
    foo();
}
