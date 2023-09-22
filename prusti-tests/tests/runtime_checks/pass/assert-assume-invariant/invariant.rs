//@run
use prusti_contracts::*;

#[trusted]
fn main() {
    let mut x = 10;
    let mut y = 0;
    while x > 0 {
        body_invariant!(x + y == 10);
        x = x - 1;
        y = y + 1;
    }
}
