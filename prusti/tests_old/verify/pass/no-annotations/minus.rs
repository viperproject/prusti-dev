extern crate prusti_contracts;

fn main() {
    let x = 10;
    let y = -x;
    assert!(y == -10);
}
