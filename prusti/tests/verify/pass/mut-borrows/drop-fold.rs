extern crate prusti_contracts;

pub struct T { f: u32, }
pub struct U { f: T, g: T, h: T, }

fn consume_T(_a: T) {}

pub fn test1(cond: bool, b: U) {
    let mut a = b;
    let x;
    if cond {
        x = &mut a.f;
        consume_T(a.g);
    } else {
        x = &mut a.h;
    }
    x.f = 5;
    // x expires here, but we cannot fold a because a.g was moved out.
}

fn main() {}
