// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// ignore-test: z3 does not support well quadratic equations

#[requires(time_credits((n * n) + 2 * n + 1))]
#[ensures(time_receipts((n * n) + 2 * n + 1))]
fn double_loop(n: usize) -> u32 {
    let mut i = 0;
    let mut res = 0;
    while i < n {
        body_invariant!(time_credits((n - i) * (n + 2)));
        body_invariant!(time_receipts(i * (n + 2)));
        res += sum(n as u32);
        i += 1;
    }
    res
}

#[requires(time_credits((n + 1) * n + 1))]
#[ensures(time_receipts((n + 1) * n + 1))]
fn two_level_loop(n: usize) -> usize {
	let mut i = 0;
	let mut res = 0;
	while i < n {
		body_invariant!(i < n);
		body_invariant!(time_credits((n + 1) * (n - i)));
		body_invariant!(time_receipts((n + 1) * i));
		let mut j = 0;
		let mut inner_res = 0;
		while j < n {
			body_invariant!(time_credits(n - j));
			body_invariant!(time_receipts(j));
			res += j;
			j += 1;
		}
		res += inner_res;
		i += 1;
	}
	res
}

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

#[requires(time_credits((n + 1) * n + 1))]
#[ensures(time_receipts((n + 1) * n + 1))]
fn two_level_loop_body_inv_end(n: usize) -> usize {
	let mut i = 0;
	let mut res = 0;
	while i < n {
		let mut j = 0;
		let mut inner_res = 0;
		while j < n {
			body_invariant!(time_credits(n - j));
			body_invariant!(time_receipts(j));
			res += j;
			j += 1;
		}
		body_invariant!(time_credits((n + 1) * (n - i - 1) + 1));
		body_invariant!(time_receipts((n + 1) * i + n));
		res += inner_res;
		i += 1;
	}
	res
}

#[requires(time_credits(1))]
fn main() {}