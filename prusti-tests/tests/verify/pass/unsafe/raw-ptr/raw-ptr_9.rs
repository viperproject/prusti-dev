use prusti_contracts::*;

fn foo() {
    let mut v = 5;
    let p = &raw mut v;
    let p_2 = bar(p);
}

#[requires(acc(*x))]
#[ensures(acc(*result))]
#[ensures(result === x)]
fn bar(x: *mut i32) -> *mut i32 {
    let res = &raw mut (*x);
    res
}
