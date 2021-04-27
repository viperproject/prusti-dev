use prusti_contracts::*;

fn main() {}

fn ref_array(a: [i32; 3]) {
    let b = &a[0];
    // it's a shared reference, so we can still access the original array during the lifetime of b
    let a0 = a[0];
    // the value behind the reference is what was in the original array
    assert!(*b == a0);
}
