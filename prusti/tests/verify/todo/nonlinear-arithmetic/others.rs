extern crate prusti_contracts;

#[requires="n < 1000"]
fn to_raw_capacity(n: usize) -> usize {
    n + n / 3
}

#[requires="0 < multiple_of && multiple_of <= 1000"]
#[requires="x / multiple_of <= 1000"]
pub fn round_up_to(x: usize, multiple_of: usize) -> usize {
    let (mut d, r) = (x / multiple_of, x % multiple_of);
    if r > 0 { d += 1; }
    d * multiple_of
}

fn slide_value(b: u16, pos: u16, bytes: u16) -> u16 {
    if b >= bytes {
        b - bytes
    } else {
        pos
    }
}

fn main() {}
