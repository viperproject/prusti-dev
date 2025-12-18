use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    let mut y = 6;
    let mut ptr = &raw mut x;
    ptr = &raw mut y;
    bar(ptr);
    assert!(x == 5);
}

#[requires(acc(x))]
fn bar(x: *mut u32){}