use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    bar(&raw mut x);
    assert!(x == 5);
}

#[requires(acc(*x))]
#[ensures(acc(*x))]
fn bar(x: *mut u32) {}
