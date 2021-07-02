use prusti_contracts::*;

fn main() {}


fn array_len() {
    let a = [0; 5];
    // this will internally do <a as &[i32]>::len(), i.e. auto-deref-coerce because `len` is a
    // method on slices, not arrays
    assert!(a.len() == 5);
}
