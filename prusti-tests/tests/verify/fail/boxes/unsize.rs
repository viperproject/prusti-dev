fn wrong_len() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    assert!(b.len() == 4); //~ ERROR: precondition might not hold
}

fn wrong_elem() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    assert!(b[0] == 2); //~ ERROR: precondition might not hold
}
