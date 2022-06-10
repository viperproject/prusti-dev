// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

struct S1 {
    x: u32,
}
fn simple_struct() {
    let mut x = S1{ x: 3};
    let mut y = &mut x;
    y.x = 3;
    x.x = 2;
}
fn simple_struct_assert_false() {
    let mut x = S1{ x: 3};
    let mut y = &mut x;
    y.x = 3;
    x.x = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
