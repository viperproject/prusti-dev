use std::cmp::Ordering;

#[derive(Eq, PartialEq)]
struct T {
    val: u32,
}

#[trusted]
fn cmp(l: &T, r: &T) -> bool {
    unimplemented!();
}

struct P {
    f: T,
}

fn should_timeout(s: &mut P, now: T) {
    if cmp(&now, &s.f) {
        s.f = now;
    }
}

fn main() {}
