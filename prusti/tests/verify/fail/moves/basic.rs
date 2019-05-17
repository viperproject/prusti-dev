extern crate prusti_contracts;

pub struct S2 {
    f: u32,
}

pub fn test4() -> S2 {
    let x = S2 {
        f: 8,
    };
    let y = x;
    assert!(y.f == 9);  //~ ERROR assert!(..) statement might not hold
    y
}

fn main() {}
