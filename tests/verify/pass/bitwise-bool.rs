extern crate prusti_contracts;

fn main() {
    let tt = true;
    let ff = false;
    // and
    assert!(tt & tt == tt);
    assert!(tt & ff == ff);
    assert!(ff & tt == ff);
    assert!(ff & ff == ff);
    // or
    assert!(tt | tt == tt);
    assert!(tt | ff == tt);
    assert!(ff | tt == tt);
    assert!(ff | ff == ff);
    // xor
    assert!(tt ^ tt == ff);
    assert!(tt ^ ff == tt);
    assert!(ff ^ tt == tt);
    assert!(ff ^ ff == ff);
}
