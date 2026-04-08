use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &raw mut x;
    bar(r_x);
    assert!(x == 5);
}

#[requires(acc(*x, 1/2))]
#[ensures(acc(*x, 1/2))]
fn bar(x: *mut i32) {}