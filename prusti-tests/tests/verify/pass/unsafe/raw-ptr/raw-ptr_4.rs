use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let mut p_x = &raw mut x;
    let p_p_x = &raw mut p_x;
    bar(p_p_x);
    assert!(x == 6);
}

#[requires(acc(x))]
#[requires(unsafe { acc(*x) })]
#[ensures(acc(x))]
#[ensures(unsafe { acc(*x) })]
#[ensures(unsafe { *x == old(*x) })]
// needed otherwise foo does not know that it can access x again, as *x (whose permission we return) of bar might point somewhere else
#[ensures(unsafe { **x == 6 } )]
fn bar(x: *mut *mut u32) {
    unsafe {
        **x = 6;
    }
}
