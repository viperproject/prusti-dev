use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let r_x = &mut x;
    let p_x = r_x as *mut i32;
    bar(p_x);
    assert!(*r_x == 6);
}

#[requires(acc(*x))]
#[ensures(acc(*x))]
#[ensures(unsafe { *x == 6 })]
fn bar(x: *mut i32) {
    unsafe {
        *x = 6;
    }
}
