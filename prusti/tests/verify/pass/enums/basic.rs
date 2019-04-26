extern crate prusti_contracts;

pub enum E1 {
    V1,
    V2,
}

pub fn test1(e: E1) {
    match e {
        E1::V1 => {},
        E1::V2 => {},
    }
}

pub enum E2 {
    V1(u32),
    V2(u32),
}

pub fn test2(e: E2) -> E2 {
    let mut e = e;
    match e {
        E2::V1(ref mut value) => {
            *value = 5;
        }
        E2::V2(ref mut value) => {
            *value = 6;
        }
    }
    e
}

fn main() {}
