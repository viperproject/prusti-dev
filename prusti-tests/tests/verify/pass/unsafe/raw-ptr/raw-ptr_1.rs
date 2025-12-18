use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let y = &raw mut x;
    let z = &raw mut x;
    bar(y, z);
    assert!(x == 6);
}

#[requires(acc(y))]
#[requires(y == z)]
#[ensures(acc(y))]
#[ensures(unsafe { *y == 6 })]
fn bar(y: *mut u32, z: *mut u32) {
    unsafe {
        *z = 6;
        assert!(*y == 6);
    }
}
