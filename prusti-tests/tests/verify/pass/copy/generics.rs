use prusti_contracts::*;

#[derive(Copy, Clone)]
pub struct S1<T> {
    f: T,
}

pub fn test1<T: Copy>(a: T) -> T {
    a
}

pub fn test2<T: Copy>(a: T) -> T {
    let b = a;
    b
}

pub fn test3<T: Copy>(a: S1<T>) -> S1<T> {
    a
}

pub fn test4<T: Copy>(a: S1<T>) -> S1<T> {
    let b = a;
    b
}

fn main() {}
