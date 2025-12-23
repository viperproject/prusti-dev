use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &raw mut x;
    bar(r_x);
    assert!(x == 5);
}

#[requires(#[prusti::frac(1/2)] acc!(*x))]
#[ensures(#[prusti::frac(1/2)] acc!(*x))]
fn bar(x: *mut i32) {}