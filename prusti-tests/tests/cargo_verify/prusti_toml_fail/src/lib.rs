use prusti_contracts::*;

#[ensures(false)]
pub fn test1() {}

pub fn test2() {
    assert!(false);
}

pub fn test3(x: usize) {
    let _y: usize = 1-x;
}
