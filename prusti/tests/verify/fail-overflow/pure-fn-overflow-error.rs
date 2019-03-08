extern crate prusti_contracts;

#[pure]
fn test_usize(x: usize) -> usize {
    x - 1 //~ ERROR overflow
}

pub fn test() {
    assert!(test_usize(123) >= 0);
}

fn main() {
}
