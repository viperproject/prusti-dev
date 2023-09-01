//@run
use prusti_contracts::*;

fn main() {
    bar((6,4));
}

#[trusted]
fn bar(mut x: (i32, i32)) {
    x.0 = 10;
    x.1 = 20;
    prusti_assert!(old(x.0 + x.1) == 10)
}
