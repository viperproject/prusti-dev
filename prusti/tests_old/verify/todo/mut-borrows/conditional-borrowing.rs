#![feature(nll)]

extern crate prusti_contracts;

fn use_node(x: &mut u32) {}

fn conditiona_borrowing(y: u32, z: u32) {
    let mut y = y;
    let mut z = z;
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
