use prusti_contracts::*;

fn main() {}


fn all_equal(a: [i32; 2]) {
    assert!(a[0] == a[1]);  //~ ERROR asserted expression might not hold
}
