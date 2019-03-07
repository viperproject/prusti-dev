extern crate prusti_contracts;

pub fn test1() {
    let mut a = 6;
    let x = &mut a;
    *x = 4;
    assert!(a == 4);
}

fn main() {}
