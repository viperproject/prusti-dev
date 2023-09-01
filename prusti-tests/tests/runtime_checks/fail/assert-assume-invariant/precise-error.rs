//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    let (x, y, z) = (5, 7, 6);
    // should fail with an additional message stating which
    // part of the conjunction failed first
    prusti_assert!(#[insert_runtime_check]x == 5 && y == 6 && z == 7);
}
