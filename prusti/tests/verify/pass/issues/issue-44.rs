extern crate prusti_contracts;

#[ensures="result == x + 1"]
fn inc(x: u32) -> u32 {
    x + 1
}

fn main() {
    let a = 5;
    let b = inc(a);
    assert!(b == 6);
}
