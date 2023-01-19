// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(n as usize + 1))]
#[ensures(time_receipts(n as usize + 1))]
fn sum(n: u32) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits((n - i) as usize));
        body_invariant!(time_receipts(i as usize));
        res += i;
        i += 1;
    }
    res
}

#[requires(time_credits(n as usize + 1))]
#[ensures(time_receipts(n as usize + 1))]
fn sum2(n: u32) -> u32 {
    let mut i = n; 
    let mut res = 0;
    while 0 < i {
        body_invariant!(time_credits(i as usize));
        body_invariant!(time_receipts((n - i) as usize));
        res += i;
        i -= 1;
    }
    res
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn foo() -> usize {
    42
}

#[requires(time_credits(n + 2))]
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
    res += foo();
    res
}

#[requires(time_credits(2 * n + 1))]
#[ensures(time_receipts(2 * n + 1))]
fn loop_foo_before_body_inv(n: usize) -> usize {
	let mut i = 0;
	let mut res = 0;
	while i < n {
		foo();
		body_invariant!(i < n);
		body_invariant!(time_credits(2 * n - 2 * i - 1));
		body_invariant!(time_receipts(2 * i + 1));
		res += 1;
		i += 1;
	}
	res
}


#[requires(time_credits(2 * n + 3))]
#[ensures(time_receipts(2 * n + 3))]
fn loop_foo_loop_foo(n: usize) -> usize {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits(n - i));
        body_invariant!(time_receipts(i));
        res += i;
        i += 1;
    }
    res += foo(); 
    while 0 < i { 
        body_invariant!(time_credits(i));
        body_invariant!(time_receipts(n - i));
        res += 1;
        i -= 1;
    }
    res += foo();
    res
}

#[requires(time_credits(12))]
#[ensures(time_receipts(12))]
fn main() {
    sum(10);
}
