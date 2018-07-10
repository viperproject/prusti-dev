#![feature(nll)]

extern crate prusti_contracts;

fn use_node(x: &mut u32) {}

fn conditiona_borrowing(mut y: u32, mut z: u32) {
    let mut b = true;
    let mut x = &mut y;
    while b {
        if b {
            x = &mut z;
        }
        b = false;
        use_node(x);
    }

}

fn main() {}
