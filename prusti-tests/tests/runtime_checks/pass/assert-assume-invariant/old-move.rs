//@run
use prusti_contracts::*;

fn main() {
    foo(43);
}

#[trusted]
fn foo(mut x: i32) {
    x = 50;
    prusti_assert!(x == 50);
    // this one fails because evaluated in old state!
    prusti_assert!(old(x == 43));
}
