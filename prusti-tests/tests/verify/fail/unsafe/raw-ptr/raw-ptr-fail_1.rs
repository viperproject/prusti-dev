use prusti_contracts::*;

fn foo() {
    let mut x = 5;
    bar(&raw mut x);
    x = 6;
}

#[requires(acc(x))]
fn bar(x: *mut u32) {}
