//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    let mut x = 10;
    let mut y = 0;
    while x >= 0 {
        body_invariant!(#[insert_runtime_check] x + y == 11);
        x = x - 1;
        y = y + 1;
    }
}
