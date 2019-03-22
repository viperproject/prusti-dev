extern crate prusti_contracts;

fn borrow(_x: &u32) {}

pub fn test1() {
    let a = 5;
    let x = &a;
    borrow(x);
}

fn main() {
}
