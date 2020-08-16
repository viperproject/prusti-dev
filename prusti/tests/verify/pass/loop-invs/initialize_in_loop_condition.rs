#![feature(box_syntax)]

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[trusted]
fn random() -> u32 {
    unimplemented!()
}

fn test() {
    let mut x: Box<u32>;

    'myloop: while {
        body_invariant!(*x < 55);
        x = box random();
        if *x == 0 {
            break 'myloop;
        }
        *x < 55
    } {
        assert!(*x != 100);
    }

    assert!(*x == 0 || *x >= 55);
}

fn main() {}
