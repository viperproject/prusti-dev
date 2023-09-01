//@run: 101
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;
#[derive(Clone)]
struct Percentage(usize);

#[trusted]
#[insert_runtime_check]
#[requires(p.0 <= 100)]
#[insert_runtime_check]
#[assert_on_expiry(*result <= 100, p.0 <= 100)]
#[insert_runtime_check]
#[ensures(old(p.0) == p.0)]
fn index_mut(p: &mut Percentage) -> &mut usize {
    &mut p.0
}

fn increment(x: &mut usize) {
    *x = *x + 1;
}

fn main() {
    // this one fails because index_mut_other is called
    foo();
}

// This testcase exists, because here the expiration location is a call
// terminator. Right after calling increment(r), r expires.
// This is handled differently than an expiration at an arbitrary statement.
#[trusted]
fn foo() {
    let mut p = Percentage(100);
    let r = index_mut(&mut p);
    increment(r);
    // r expires here, and is too high, so the check fails
    println!("p now has value: {}", p.0);
}

