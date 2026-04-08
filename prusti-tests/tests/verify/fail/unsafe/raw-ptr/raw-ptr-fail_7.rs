use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &raw mut x;
    bar(r_x);
}

#[requires(acc(*x, Real::from_f64(0.5)))]
fn bar(x: *mut i32) {
    unsafe {
        *x = 6;
    }
}