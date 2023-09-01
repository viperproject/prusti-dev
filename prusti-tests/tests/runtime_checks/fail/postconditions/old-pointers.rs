//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    let mut x = 5;
    let mut y = 6;
    swap(&mut x, &mut y);
    println!("function executed to the end");
}

// specifications are checked in reverse order (apparently)
// to check that both specifications are checked at runtime,
#[trusted]
#[insert_runtime_check]
#[ensures(old(*x) == *y && old(*y) == *x)]
fn swap(x: &mut i32, y: &mut i32) {
    let z = *x;
    // this causes postcondition to fail
    *x = *y + 1;
    *y = z;
}
