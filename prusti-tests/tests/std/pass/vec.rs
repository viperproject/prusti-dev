use prusti_contracts::*;

fn main() {
    let mut v = Vec::new();
    assert!(v.is_empty());
    assert!(v.len() == 0);

    v.push(10);
    assert!(!v.is_empty());
    assert!(v.len() == 1);
    // issue #1221:
    //let slice = v.as_slice();
    //assert!(slice[0] == 10);

    v.push(20);
    assert!(v.len() == 2);
    //let slice = v.as_slice();
    //assert!(slice[0] == 10);
    //assert!(slice[1] == 10);

    v.clear();
    assert!(v.is_empty());
}
