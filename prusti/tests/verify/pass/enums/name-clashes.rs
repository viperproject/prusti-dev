extern crate prusti_contracts;

pub enum E {
    V1,
    V2,
}

pub struct S {
    enum_0: u32,
    enum_1: u32,
}

pub fn test1(e: E) {
    match e {
        E::V1 => {},
        E::V2 => {},
    }
    let mut x = S {
        enum_0: 0,
        enum_1: 1,
    };
    x.enum_0 = 4;
}

fn main() {}

