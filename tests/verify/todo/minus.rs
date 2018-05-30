extern crate prusti_contracts;

fn main() {
    let x = 10;
    let y = -x;
    println!("{}", y as u32);
    assert!(y == -10);
}
