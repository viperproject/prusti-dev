extern crate prusti_contracts;

#[requires="a + b <= std::u32::MAX"]
#[ensures="result == a + b"]
fn sum(a: u32, b: u32) -> u32 {
    a + b
}

#[ensures="
    match result {
        Some(r) => r == a + b,
        None => true,
    }
"]
fn sum_call(a: u32, b: u32) -> Option<u32> {
    if a <= std::u32::MAX - b {
        Some(sum(a, b))
    } else {
        None
    }
}

fn main() {}
