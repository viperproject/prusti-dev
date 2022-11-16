use prusti_contracts::*;

pub struct S1 {}

pub fn test1() -> S1 {
    let x = S1 {};
    x
}

pub struct S2 {
    f: u32,
}

pub fn test2() -> S2 {
    let x = S2 {
        f: 8,
    };
    x
}

pub fn test3() -> S2 {
    let x = S2 {
        f: 8,
    };
    let y = x;
    assert!(y.f == 8);
    y
}

pub fn test5() {
    let x = 4;
    let y = x;
}


fn main() {}
