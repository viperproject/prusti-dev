use prusti_contracts::*;

fn main() {}

#[requires(a[0..2] == [0, 0])]
pub fn foo(a: [i32; 5]) {
    assert!(a[0] == 0);
    assert!(a[1] == 0);
}
