extern crate prusti_contracts;

pub enum E {
    V1,
    V2,
}

pub fn test1(e: E) {
    match e {
        E::V1 => {},
        E::V2 => {},
    }
}

fn main() {}
