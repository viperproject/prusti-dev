use prusti_contracts::*;

pub struct T { f: u32, }
pub struct U { f: T, g: T, h: T, }

fn consume_T(_a: T) {}
fn consume_U(_a: U) {}

/// In this example, without consulting the DAG we would restore
/// permissions that were actually dropped:
pub fn test1(cond1: bool, cond2: bool, b: U) {
    let mut a = b;
    let x;
    if cond1 {
        x = &mut a.f;
    } else {
        x = &mut a.h;
    }
    if cond2 {
        consume_T(a.g)
    }
    x.f = 5;
}

pub fn test2(b: U) {
    let mut a = b;
    let f = &mut a.f;
    let g = &mut a.g;
    use_both(f, g);
    consume_U(a);
}

fn use_both(_f: &mut T, _g: &mut T) {
}

fn main() {}
