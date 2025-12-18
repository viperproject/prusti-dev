use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let mut r_x = &mut x;
    let p_r_x = &raw mut r_x;
    bar(p_r_x);
    assert!(x == 5);
}

#[requires(acc(x))]
fn bar(x: *mut &mut u32) {
    unsafe {
        **x = 6;
    }
}
