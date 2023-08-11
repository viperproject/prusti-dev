// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(n > 0)]
#[requires(time_credits(n as usize + 2))]
#[ensures(time_receipts(n as usize + 1))] // This is also an error but the other is reported first.
fn sum(n: u32) -> u32 {
    let mut i = 1; // To be correct it should be n
    let mut res = 0;
    while 0 < i {
        body_invariant!(time_credits(i as usize)); //~ ERROR Not enough time receipts for invariant in the first loop iteration.
        body_invariant!(time_receipts((n - i) as usize));
        res += i;
        i -= 1;
    }
    res
}

#[requires(time_credits(3))]
fn sum2(n: usize) -> usize {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits(1)); //~ ERROR Not enough time credits
        i += 1;
        res += i;
    }
    res
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn foo() -> usize {
    42
}

#[requires(time_credits(n + 1))] // should be n + 2 to be correct
#[ensures(time_receipts(n + 2))]
fn loop_foo(n: usize) -> usize {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits(n - i));
        body_invariant!(time_receipts(i));
        res += i;
        i += 1;
    }
    res += foo(); //~ ERROR Not enough time credits to call function.
    res
}

#[requires(time_credits(2 * n + 1))] // should be 2 * n + 2 to be correct
#[ensures(time_receipts(2 * n + 2))]
fn loop_foo_loop(n: usize) -> usize {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits(n - i));
        body_invariant!(time_receipts(i));
        res += i;
        i += 1;
    }
    res += foo(); // this is also an error but the other is reported first.
    while 0 < i {
        body_invariant!(time_receipts(n - i)); //~ ERROR Not enough time credits
        body_invariant!(time_credits(i));
        res += 1;
        i -= 1;
    }
    res
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn main() {}
