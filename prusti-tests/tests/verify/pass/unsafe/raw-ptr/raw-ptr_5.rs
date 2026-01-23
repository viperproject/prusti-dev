use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &raw mut x;
    let r = Real::from(0.5);
    assert!(r == Real::from(0.5));
    bar(r_x, r);
    assert!(x == 5);
}

#[requires(acc(*x, 1.0/2.0))]
#[requires(r == Real::new(1,2))]
#[ensures(acc(*x, r))]
fn bar(x: *mut i32, r: Real) {}