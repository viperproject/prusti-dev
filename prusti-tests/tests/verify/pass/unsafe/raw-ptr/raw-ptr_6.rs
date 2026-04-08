use prusti_contracts::*;

pub fn foo() {
    let mut v = 5;
    let tmp = &mut v;
    let x = tmp as *mut i32;
    let y = bar(x);
    unsafe {
        *y = 2;
        *x = 1;
    }
    assert!(*tmp == 1);
    assert!(v == 1);
}

#[requires(acc(*x))]
#[ensures(x === result)]
#[ensures(acc(*x))]
fn bar(x: *mut i32) -> *mut i32 {
    x
}
