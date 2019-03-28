#[derive(Eq, PartialEq)]
pub struct T {
    val: u32,
}

#[trusted]
fn cmp(_l: &T, _r: &T) -> bool {
    unimplemented!();
}

pub struct P {
    f: T,
}

pub fn test1(s: &mut P, now: T) {
    if cmp(&now, &s.f) {
        s.f = now;
    }
}

pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

#[trusted]
pub fn foo<T>(_a: T, _b: T) -> T {
    unimplemented!();
}

pub fn test2<T: Copy>(x: &Pair<T>) -> T {
    foo(x.first, x.second)
}

fn main() {}
