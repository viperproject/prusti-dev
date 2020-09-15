use prusti_contracts::*;

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

pub enum E3<T> {
    V1(T),
    V2(T),
}

pub fn test3<T>(e: &mut E3<T>) -> &mut T {
    match *e {
        E3::V1(ref mut b) => b,
        E3::V2(ref mut b) => b,
    }
}

pub enum E4 {
    V1,
    V2,
    V3
}

pub fn test4() -> E4 {
    if false {
        E4::V1
    } else if false {
        E4::V2
    } else {
        E4::V3
    }
}

fn main() {}
